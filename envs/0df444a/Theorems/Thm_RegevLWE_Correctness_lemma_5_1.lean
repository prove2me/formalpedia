-- Prove2me | Theorems.Thm_RegevLWE_Correctness_lemma_5_1
-- name    : RegevLWE.Correctness.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:46.653428+00:00
-- url     : https://prove2.me/theorems/372c2ee4-3a66-4998-824d-787044393416
-- title:
--   Lemma 5.1 (Correctness), p. 34:35 — if Pr_{χ^⋆k}[|e| < ⌊p/2⌋/2] > 1 − δ for all k ≤ m, decryption is correct with probability ≥ 1 − δ
-- statement:
--   Let $p \ge 2$ and $n, m \ge 0$ be integers, let $\chi$ be a probability distribution on $\mathbb Z_p$, and let $\delta > 0$. For $a \in \mathbb Z_p$ let $|a|$ be its distance from $0$ modulo $p$, and let $\chi^{\star k}$ be the distribution of the sum of $k$ independent samples from $\chi$ ($\chi^{\star 0}$ the point mass at $0$). Assume that for every $k \in \{0, 1, \dots, m\}$,
--   $$\Pr_{e \sim \chi^{\star k}}\Bigl[\,|e| < \Bigl\lfloor \frac p2 \Bigr\rfloor \Big/ 2\,\Bigr] > 1 - \delta .$$
--   Then the probability of decryption error of Regev's cryptosystem with parameters $n, m, p, \chi$ is at most $\delta$: for each bit $c \in \{0, 1\}$, if the private key $s$ is chosen uniformly in $\mathbb Z_p^n$, the public key $(a_i, \langle a_i, s\rangle + e_i)_{i=1}^m$ is formed with $a_i$ independent and uniform in $\mathbb Z_p^n$ and $e_i$ independent with law $\chi$, $c$ is encrypted with a uniformly random subset $S \subseteq [m]$, and the result is decrypted with $s$, then
--   $$\Pr[\text{outcome} = c] \ge 1 - \delta ,$$
--   the probability being over all of $s$, $a_1, \dots, a_m$, $e_1, \dots, e_m$ and $S$.
--
--   This is the correctness half of Regev's LWE-based public-key cryptosystem: it turns a tail bound on the noise distribution into a bound on the decryption error. For the paper's parameters, Claim 5.2 supplies the hypothesis with a negligible $\delta$.
--
--   **Formalization Note** The hypothesis and conclusion are stated in $\mathbb R$, with probabilities taken as `toReal` of `PMF` masses (exact, since they are at most $1$). An $\mathbb R_{\ge 0}^{\infty}$ form with `ENNReal.ofReal (1 − δ) <` was rejected: for $\delta \ge 1$ it would demand a positive probability, a hypothesis the page does not make. $p \ge 2$ is the paper's standing range for $\mathbb Z_p$ (p. 34:14); primality, which the paper's parameter choice includes, is not assumed, since the lemma does not use it. $\lfloor p/2\rfloor/2$ is a real number.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:35, Lemma 5.1 (Correctness); protocol on p. 34:35; ℤ_p for p ≥ 2 on p. 34:14

import Mathlib
import Definitions.Def_RegevLWE_Correctness_Cryptosystem

open Matrix

namespace RegevLWE.Correctness

/-- Lemma 5.1 (Correctness), Regev, J. ACM 2009, p. 34:35. Let `p ≥ 2`, `n, m ≥ 0`, `χ` a
probability distribution on `ℤ_p` and `δ > 0`. Assume that for every `k ∈ {0, 1, …, m}`,
`Pr_{e∼χ^⋆k}[|e| < ⌊p/2⌋/2] > 1 − δ`. Then for any bit `c ∈ {0, 1}`, if the private key, the
public key and the subset `S` are chosen as in the protocol, `c` is encrypted and the result
decrypted, the outcome is `c` with probability at least `1 − δ`. The probability is over all of
the protocol's randomness: `s`, `a₁, …, a_m`, `e₁, …, e_m` and `S`. -/
theorem lemma_5_1 {p : ℕ} [NeZero p] (hp : 2 ≤ p) (n m : ℕ) (χ : PMF (ZMod p)) (δ : ℝ)
    (hδ : 0 < δ)
    (hχ : ∀ k ≤ m, 1 - δ <
      ((convPow χ k).toOuterMeasure {e | (absZ e : ℝ) < ((p / 2 : ℕ) : ℝ) / 2}).toReal)
    (c : Fin 2) :
    1 - δ ≤ (outcome n m χ c c).toReal := by sorry

end RegevLWE.Correctness
