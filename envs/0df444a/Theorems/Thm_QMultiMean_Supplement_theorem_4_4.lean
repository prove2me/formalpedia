-- Prove2me | Theorems.Thm_QMultiMean_Supplement_theorem_4_4
-- name    : QMultiMean.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:16:37.931873+00:00
-- url     : https://prove2.me/theorems/08ec9db9-a77c-4cc6-944d-913bcd770247
-- title:
--   Theorem 4.4 — low-precision phase-oracle estimator: $\|\tilde\mu-\mu\|_\infty\le\max\{1/\sqrt n,\,d/n'\}\log(d/\delta)$
-- statement:
--   Let $d\in\mathbb N$, $\delta\in(0,1)$, and let $n\ge\log(d/\delta)$ and $n'\ge\sqrt d\log(d/\delta)$ be reals. There is a quantum estimator in the phase-oracle model, chosen from $d,n,n',\delta$ and the sample set only, with the following property. For every random variable $X$ with values in $[-1/4,1/4]^d$ and mean $\mu=\mathbb E[X]$, and every quantum experiment $U_{\mathbb P}$, it outputs $\tilde\mu$ with
--   $$\|\tilde\mu-\mu\|_\infty\ \le\ \max\Big\{\frac{1}{\sqrt n},\frac{d}{n'}\Big\}\cdot\log\Big(\frac d\delta\Big)$$
--   with probability at least $1-\delta$. It uses $\tilde O(n)$ calls to $U_{\mathbb P}$ and $\tilde O(n')$ calls to $\mathcal P_X$.
--
--   When $n<d$ this beats Theorem 4.3: the estimator (Algorithm 4, $\mathsf{QLowPrecPhase}_d$) runs Algorithm 3 on an empirical distribution of $O(n)$ classical samples.
--
--   **Formalization Note** $\tilde O$ as in Theorem 4.3. As printed, there is no hypothesis $n<d$.
--
--   Differences from the source:
--   - reading: the estimator QLowPrecPhase_d(X, n, n′, δ) (Algorithm 4) finds µ̃ … → there exists a PhaseEstimator, built from d, n, n′, δ and N only, with the stated counts and guarantee for every PMF P, every X with values in [−1/4,1/4]^d and every U_P meeting Definition 2.5; reason: the content of the theorem is the guarantee; the named algorithm is one witness (the same reading as the published Theorems 3.3–3.4)
--   - reading: a quantum algorithm with access to U_P (Definition 2.5) and the phase oracle P_X (Definition 2.7); no formal model in the paper → a PhaseEstimator: oracle circuit on copies of H_Ω ⊗ ℂ^d plus an ancilla, uncontrolled U_P/U_P⁻¹ calls on the sample register, P_X/P_X⁻¹ calls controlled by an ancilla label set, computational-basis measurement and a classical output map; built before the instance; reason: mirrors the published binary-oracle Estimator; the paper uses controlled calls of P_X (p.17, Lemma 2.12), and without control X and X + c·1 are indistinguishable
--   - reading: Õ(n) calls to U_P and Õ(n′) calls to P_X → at most C·max(1,n)·(1+log(1+n)+log d)^k calls to U_P/U_P⁻¹ and C·max(1,n′)·(1+log(1+n′)+log d)^k calls to P_X/P_X⁻¹, with universal C, k chosen first, uniformly in δ; reason: the published base items' reading of Õ for real n; max(1,·) matters only for d = 1, since for d ≥ 2 the hypotheses give n ≥ log 2 and n′ ≥ √2·log 2, where max(1,·) ≤ 2·(·) is absorbed in C
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, pp.22–23, Theorem 4.4

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_Supplement_phaseOracle
import Definitions.Def_QMultiMean_Supplement_PhaseCircuit

set_option autoImplicit false

namespace QMultiMean.Supplement

open QMultiMean

/-- Theorem 4.4 (Low-precision analog mean estimator) of Cornelissen, Hamoudi, Jerbi,
*Near-Optimal Quantum Algorithms for Multivariate Mean Estimation*, arXiv:2111.09787v2, pp.22–23:
for `d ∈ ℕ`, `δ ∈ (0, 1)`, `n ≥ log(d/δ)`, `n′ ≥ √d log(d/δ)` and `X` a random variable with values
in `[−1/4, 1/4]^d` with `µ = E[X]`, the estimator `QLowPrecPhase_d` (Algorithm 4) finds `µ̃` that
with probability at least `1 − δ` satisfies `‖µ̃ − µ‖∞ ≤ max{1/√n, d/n′} · log(d/δ)`, with `Õ(n)`
calls to `U_P` and `Õ(n′)` calls to `P_X`.

**Formalization Note.** A quantum estimator is a `PhaseEstimator` (oracle circuit
with uncontrolled `U_P`/`U_P⁻¹` calls and controlled `P_X`/`P_X⁻¹` calls, computational-basis
measurement, classical output map), built from the parameters and the sample set `Ω = Fin (N+1)`
before the instance; success is required for the probability mass function `P`, every `X` with
values in `[−1/4, 1/4]^d` (every coordinate of every value) and every quantum experiment `U_P` meeting
Definition 2.5 (the phase oracle `P_X` of Definition 2.7 is determined by `X`). `Õ(n)` calls to `U_P`
and `Õ(n′)` calls to `P_X` are `C·max(1, n)·(1 + log(1+n) + log d)^k` and
`C·max(1, n′)·(1 + log(1+n′) + log d)^k` with universal `C, k` chosen first (natural log), as in the
published base items. `log` is the natural logarithm. `d = 0` is allowed (the statement is then
trivially true). The algorithm is asserted to exist (Algorithm 4 is one witness). The statement has no
hypothesis `n < d`, as printed. -/
theorem theorem_4_4 :
    ∃ C : ℝ, ∃ k : ℕ, ∀ d : ℕ, ∀ (δ n n' : ℝ), 0 < δ → δ < 1 →
      Real.log (d / δ) ≤ n → Real.sqrt d * Real.log (d / δ) ≤ n' →
      ∀ N : ℕ, ∃ M : PhaseEstimator N d (Vec d),
        (M.numU : ℝ) ≤ C * max 1 n * (1 + Real.log (1 + n) + Real.log d) ^ k ∧
        (M.numPh : ℝ) ≤ C * max 1 n' * (1 + Real.log (1 + n') + Real.log d) ^ k ∧
        ∀ (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d), IsPMF P →
          (∀ ω j, |X ω j| ≤ 1 / 4) →
          ∀ U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, IsQuantumExperiment P U →
            1 - δ ≤ M.successProb U X
              {est | supNorm (est - mean P X) ≤
                max (1 / Real.sqrt n) (d / n') * Real.log (d / δ)} := by sorry

end QMultiMean.Supplement
