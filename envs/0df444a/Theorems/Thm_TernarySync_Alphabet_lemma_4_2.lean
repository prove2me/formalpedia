-- Prove2me | Theorems.Thm_TernarySync_Alphabet_lemma_4_2
-- name    : TernarySync.Alphabet.lemma_4_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T03:54:41.126344+00:00
-- url     : https://prove2.me/theorems/521aec8e-7691-4e8f-8030-fdd65d21b842
-- title:
--   Lemma 4.2 — conditional point mass: $s \ge \ell/18 - 2$, $Y$ is fixed, $\Pr[X = x \mid F = f] \le 2^{-s} \le 4\exp(-(\log 2/18)\ell)$
-- statement:
--   Fix a square-free outer word $T$ of length $N$ over $\{0,1,2\}$, let $R$ be uniform on $\{0,1\}^N$ (independent fair bits) and $W = W(T,R)$. Let $\ell > 1000$ be an integer and $t$ an available start, and put $X = W[t, t+\ell)$, $Y = W[t+\ell, t+2\ell)$. Let $I_X$ index the macroblocks contained completely in $X$, put $s = |I_X|$, and let $F = (R_i)_{i \notin I_X}$. Then $s \ge \ell/18 - 2$, and for every outcome $f$ of $F$ of positive probability, $Y$ is fixed on the event $\{F = f\}$ and
--
--   $$\Pr[X = x \mid F = f] \le 2^{-s} \le 4 \exp\!\Big(-\frac{\log 2}{18}\,\ell\Big) \qquad \text{for every } x \in \{0,1,2\}^\ell. \tag{10}$$
--
--   Exposing every choice except those of the complete blocks inside $X$ fixes the neighbour $Y$ but leaves linearly many independent fair choices inside $X$; this point-mass bound is the only property of the random source the proof of Theorem 4.1 uses.
--
--   **Formalization Note.** Indices are 0-based; $t$ is available when $t + 2\ell \le 18N$. $\log$ is the natural logarithm. An outcome $f$ is given as a full vector `f : Fin N → Fin 2` whose values on $I_X$ are ignored; the event $F = f$ is `agreeOff I_X f`, and "$Y$ is fixed" is: every $R$ in that event gives the same $Y$ as $f$ itself. $\Pr[\,\cdot \mid F = f]$ is the count ratio `condProb`, which is the conditional probability of the uniform measure.
--
--   Differences from the source:
--   - encoding: 1-based half-open factors $S[i,j)$ with $1 \le i \le j \le n+1$ → 0-based `factor S i j` = positions $i,\dots,j-1$, so the ranges shift by one (e.g. $k \le n+1$ becomes $k \le n$); reason: index shift only; the same factors and the same instances
--   - encoding: R independent fair bits; Pr[X = x | F = f] → the count ratio condProb under the uniform probability |A|/2^N on Fin N → Fin 2; reason: the uniform measure on a finite set is the count ratio
--   - encoding: every outcome f of F of positive probability → every f : Fin N → Fin 2, with F = f encoded as agreement with f outside I_X; reason: every outcome has probability 2^(s−N) > 0, so the restriction excludes nothing; the values of f on I_X are irrelevant
--   - encoding: Y is fixed (given F = f) → every R agreeing with f outside I_X gives blockY T R t ℓ = blockY T f t ℓ; reason: Y is constant on the event F = f
--   - encoding: the standing setting of §4: T a fixed finite square-free outer word, ℓ > L = 1000 an integer, t an available start → hypotheses IsSquareFree T, 1000 < ℓ, t + 2ℓ ≤ 18|T|; reason: the section's standing assumptions (p. 15) written as binders
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 15 (PDF 16), Lemma 4.2, Eq. (10)

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Lemma 4.2 (p. 15). Fix a square-free outer word `T` of length `N`, an integer `ℓ > 1000` and
an available start `t` (0-based, `t + 2ℓ ≤ 18 N`); `X = W[t, t + ℓ)`, `Y = W[t + ℓ, t + 2ℓ)`.
Let `I_X` be the macroblocks contained completely in `X`, `s = |I_X|`, and `F = (R_i)_{i ∉ I_X}`.
Then `s ≥ ℓ/18 − 2`, and for every outcome `f` of `F` (each has positive probability), `Y` is
fixed on `{F = f}` and `Pr[X = x | F = f] ≤ 2^{−s} ≤ 4 exp(−(log 2/18) ℓ)` for every
`x ∈ {0, 1, 2}^ℓ`, under independent fair bits `R`. -/
theorem lemma_4_2 (T : List (Fin 3)) (hT : IsSquareFree T) (t ℓ : ℕ) (hℓ : 1000 < ℓ)
    (ht : t + 2 * ℓ ≤ 18 * T.length) :
    (ℓ : ℝ) / 18 - 2 ≤ ((completeBlocks T.length t ℓ).card : ℝ) ∧
      ∀ f : Fin T.length → Fin 2,
        (∀ R ∈ agreeOff (completeBlocks T.length t ℓ) f, blockY T R t ℓ = blockY T f t ℓ) ∧
        ∀ x : List (Fin 3), x.length = ℓ →
          condProb {R | blockX T R t ℓ = x} (agreeOff (completeBlocks T.length t ℓ) f) ≤
              (2 : ℝ) ^ (-((completeBlocks T.length t ℓ).card : ℝ)) ∧
            (2 : ℝ) ^ (-((completeBlocks T.length t ℓ).card : ℝ)) ≤
              4 * Real.exp (-(Real.log 2 / 18) * (ℓ : ℝ)) := by sorry

end TernarySync.Alphabet
