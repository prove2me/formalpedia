-- Prove2me | Theorems.Thm_QMultiMean_Supplement_theorem_4_5
-- name    : QMultiMean.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:17:19.982294+00:00
-- url     : https://prove2.me/theorems/d5bb6fdc-0c0e-480c-8488-6e6673b99878
-- title:
--   Theorem 4.5 — phase-oracle mean estimation in all regimes, in $\ell_\infty$ and (times $d^{1/p}$) in $\ell_p$
-- statement:
--   Let $d,n,n'\in\mathbb N$ and $\delta\in(0,1)$. There is a quantum estimator in the phase-oracle model, chosen from $d,n,n',\delta$ and the sample set only, using $\tilde O(n)$ calls to $U_{\mathbb P}$ and $\tilde O(n')$ calls to $\mathcal P_X$, such that for every random variable $X$ with values in $[-1/4,1/4]^d$ and mean $\mu$, and every quantum experiment $U_{\mathbb P}$, the output $\tilde\mu$ satisfies, with probability at least $1-\delta$,
--   $$\|\tilde\mu-\mu\|_\infty\le B:=\begin{cases}1,&\text{if } n'<d\text{ or } n<\log(d/\delta),\\[2pt] \max\{1/\sqrt n,\,d/n'\}\cdot\log(d/\delta),&\text{if } n'\ge d\text{ and }\log(d/\delta)\le n<d,\\[2pt] \max\{\sqrt d/n,\,d/n'\}\cdot\log(d/\delta),&\text{if } n'\ge d\text{ and } n\ge d.\end{cases}$$
--   Furthermore, for every $p\in[1,\infty)$, the same estimator satisfies $\|\tilde\mu-\mu\|_p\le d^{1/p}B$ with probability at least $1-\delta$.
--
--   This collects the upper bounds of Section 4 in one statement; Theorem 4.10 shows that each regime is optimal up to polylogarithmic factors.
--
--   **Formalization Note** Since $n,n'$ are integers, $\tilde O(n)$ is $Cn(1+\log(1+n)+\log d)^k$ with universal $C,k$; $n=0$ means no calls.
--
--   Differences from the source:
--   - reading: the estimator "we can find an approximation µ̃" finds µ̃ … → there exists a PhaseEstimator, built from d, n, n′, δ and N only, with the stated counts and guarantee for every PMF P, every X with values in [−1/4,1/4]^d and every U_P meeting Definition 2.5; reason: the content of the theorem is the guarantee; the named algorithm is one witness (the same reading as the published Theorems 3.3–3.4)
--   - reading: a quantum algorithm with access to U_P (Definition 2.5) and the phase oracle P_X (Definition 2.7); no formal model in the paper → a PhaseEstimator: oracle circuit on copies of H_Ω ⊗ ℂ^d plus an ancilla, uncontrolled U_P/U_P⁻¹ calls on the sample register, P_X/P_X⁻¹ calls controlled by an ancilla label set, computational-basis measurement and a classical output map; built before the instance; reason: mirrors the published binary-oracle Estimator; the paper uses controlled calls of P_X (p.17, Lemma 2.12), and without control X and X + c·1 are indistinguishable
--   - reading: Õ(n) calls to U_P and Õ(n′) calls to P_X, n, n′ ∈ ℕ → at most C·n·(1+log(1+n)+log d)^k and C·n′·(1+log(1+n′)+log d)^k calls, universal C, k chosen first, uniformly in δ; reason: the published base items' reading of Õ; for integer n no max(1,·) is needed, and n = 0 means zero calls
--   - reading: the same performance guarantees on ‖µ̃ − µ‖_p, multiplied with d^{1/p} → the same estimator satisfies each ℓ_p bound with probability at least 1 − δ, for every p ≥ 1; reason: the paper derives the ℓ_p clause from the ℓ∞ output by ‖x‖_p ≤ d^{1/p}‖x‖∞
--   - reading: the printed cases overlap (n′ ≥ d, n ≥ d and n < log(d/δ) satisfies both the first and the third) → the cases are tested in printed order, so the overlap gets the bound 1; reason: there log(d/δ)/n > 1, so the third case's bound max{√d/n, d/n′}·log(d/δ) ≥ √d ≥ 1 and the Lean bound 1 implies both printed bounds
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, pp.23–24, Theorem 4.5

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_Supplement_phaseOracle
import Definitions.Def_QMultiMean_Supplement_PhaseCircuit
import Definitions.Def_QMultiMean_Supplement_lpNorm

set_option autoImplicit false

namespace QMultiMean.Supplement

open QMultiMean

/-- Theorem 4.5 of Cornelissen, Hamoudi, Jerbi, *Near-Optimal Quantum Algorithms for Multivariate
Mean Estimation*, arXiv:2111.09787v2, pp.23–24: for `d, n, n′ ∈ ℕ`, `δ ∈ (0, 1)` and `X` a random
variable with values in `[−1/4, 1/4]^d` with `µ = E[X]`, one can find `µ̃` that with probability
at least `1 − δ` satisfies `‖µ̃ − µ‖∞ ≤ 1` if `n′ < d` or `n < log(d/δ)`;
`≤ max{1/√n, d/n′} · log(d/δ)` if `n′ ≥ d` and `log(d/δ) ≤ n < d`;
`≤ max{√d/n, d/n′} · log(d/δ)` if `n′ ≥ d` and `n ≥ d`; with `Õ(n)` calls to `U_P` and `Õ(n′)`
calls to `P_X`. Furthermore, for all `p ∈ [1, ∞)`, the same guarantees hold for `‖µ̃ − µ‖_p`,
multiplied by `d^{1/p}`.

**Formalization Note.** A quantum estimator is a `PhaseEstimator` (oracle circuit
with uncontrolled `U_P`/`U_P⁻¹` calls and controlled `P_X`/`P_X⁻¹` calls, computational-basis
measurement, classical output map), built from the parameters and the sample set `Ω = Fin (N+1)`
before the instance; success is required for the probability mass function `P`, every `X` with
values in `[−1/4, 1/4]^d` (every coordinate of every value) and every quantum experiment `U_P` meeting
Definition 2.5 (the phase oracle `P_X` of Definition 2.7 is determined by `X`). `Õ(n)` calls to `U_P`
and `Õ(n′)` calls to `P_X` are `C·n·(1 + log(1+n) + log d)^k` and `C·n′·(1 + log(1+n′) + log d)^k`
with universal `C, k` chosen first (natural log), as in the published base items (there with
`max(1, n)` for real `n`; here `n, n′` are integers, so no `max` is needed and `n = 0` means zero
calls). `log` is the natural logarithm. `d = 0` is allowed (the
statement is then trivially true). One estimator per `(d, n, n′, δ, N)` meets the `ℓ∞` bound and, for every `p ≥ 1`,
the `ℓ_p` bound times `d^{1/p}`, each with probability at least `1 − δ`. `n, n′` are natural
numbers, `0` included. -/
theorem theorem_4_5 :
    ∃ C : ℝ, ∃ k : ℕ, ∀ d : ℕ, ∀ (n n' : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ N : ℕ, ∃ M : PhaseEstimator N d (Vec d),
        (M.numU : ℝ) ≤ C * n * (1 + Real.log (1 + n) + Real.log d) ^ k ∧
        (M.numPh : ℝ) ≤ C * n' * (1 + Real.log (1 + n') + Real.log d) ^ k ∧
        ∀ (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d), IsPMF P →
          (∀ ω j, |X ω j| ≤ 1 / 4) →
          ∀ U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, IsQuantumExperiment P U →
            let bound : ℝ :=
              if (n' : ℝ) < d ∨ (n : ℝ) < Real.log (d / δ) then 1
              else if (n : ℝ) < d then
                max (1 / Real.sqrt n) (d / n') * Real.log (d / δ)
              else
                max (Real.sqrt d / n) (d / n') * Real.log (d / δ)
            1 - δ ≤ M.successProb U X {est | supNorm (est - mean P X) ≤ bound} ∧
            ∀ p : ℝ, 1 ≤ p →
              1 - δ ≤ M.successProb U X
                {est | lpNorm p (est - mean P X) ≤ (d : ℝ) ^ (1 / p) * bound} := by sorry

end QMultiMean.Supplement
