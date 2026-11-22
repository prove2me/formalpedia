-- Prove2me | Theorems.Thm_SelfSelReg_Supplement_theorem_6_3
-- name    : SelfSelReg.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:18:32.06892+00:00
-- url     : https://prove2.me/theorems/a62f35b2-bf8a-46c4-a988-a2aca9e0c5b4
-- title:
--   Theorem 6.3 — projected-moment accuracy
-- statement:
--   Consider the Gaussian self-selection model with regressors $w_1,\dots,w_k\in\mathbb R^n$, $2\le k\le n$, under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, and the hyperparameters $K$, $s$, $T$ of the paper. Fix a recovered list $\widehat{\mathcal R}$ matched bijectively to $R\subsetneq[k]$ with $\|\widehat w-w_{\mathrm{match}(\widehat w)}\|_2\le e^{-K^6s}$ for every $\widehat w\in\widehat{\mathcal R}$, and put $Q=[k]\setminus R$. For $\delta\in(0,1/3)$, run ESTIMATEPROJECTEDMOMENTS with sampling accuracy $e^{-K^6s}$, failure probability $\delta$ and fresh observations independent of $\widehat{\mathcal R}$. With probability at least $1-\delta$, the returned symmetric matrices $\widehat A,\widehat M_1,\dots,\widehat M_n$ form an $e^{-K^2s}$-estimate of the projected moment matrices for $Q$ relative to the constructed map $C_s$ (Definition 6.2), and
--
--   $$
--   \bigl\|(I-C_s^\top C_s)(A_Q^{(s)})^{1/2}\bigr\|_{\mathrm{op}}^2\le2K^{s-1}e^{-K^2s}\operatorname{tr}(A_Q^{(s)}).
--   $$
--
--   Its sample complexity is $\widetilde O\bigl((nk)^{O(K^{10})}\log(1/\delta)\bigr)$ and its running time is $(nk)^{\mathrm{poly}(K)}\log(1/\delta)$.
--
--   The theorem supplies the two inputs of the observable-operator construction (Theorem 6.5): accurate projected even and odd moments of order $s$ and $2s+1$, and a projection $C_s$ that loses little of the even target, without ever forming a tensor with $n^s$ entries.
--
--   **Formalization Note** The routine is a program of the sampling real RAM of the base mission, restricted to exact arithmetic, comparisons, fair coins and sample reads, fixed with one constant $C$ before all parameters; resource bounds as in Theorem 6.1. The returned matrices are $|Q|\times|Q|$ (the dimension rule of Algorithm 6.1 gives $p_s=|Q|$) and are symmetric on every run. On the success event there is a map $C_s\in\mathbb R^{|Q|\times n^s}$ with orthonormal rows for which both conclusions hold. $(A_Q^{(s)})^{1/2}$ is the positive semidefinite square root.
--
--   Differences from the source:
--
--   - reading: "ESTIMATEPROJECTEDMOMENTS (Algorithm 6.1) returns …", "its sample complexity is …", "its running time is …", with no machine named; the pseudocode uses exact eigendecompositions, the Gaussian CDF, square roots and logarithms as steps → one program of the published sampling real RAM restricted to + − × ÷, comparisons, fair coins and the sample instruction (ArithmeticCoin), chosen with one constant C before every parameter and instance, whose output has the stated guarantee and whose samples and work obey the stated bounds on every coin tape and sample stream; reason: this is the reading of the published goal Theorem 1.3 of the same paper; admitting a unit-cost eigensolver, CDF, square root or logarithm would make the existence of the routine a weaker claim, and the conclusion here is an inequality with a positive error, which an approximate computation of those steps can meet
--   - reading: the returned matrices form an estimate "relative to the constructed map C_s", a map built inside Algorithm 6.1 and not returned by it → on the success event there exists a map C_s with orthonormal rows for which the estimate and the projection-error bound both hold; reason: the output of the routine is Â, M̂_1, …, M̂_n only; Theorem 6.5 uses C_s only through these two properties
--   - encoding: p_s × p_s matrices with p_1 = n, p_{r+1} = min{k − |R̂|, p_r n} → |Q| × |Q| matrices, |Q| = k − |R̂|; reason: since |Q| ≤ k ≤ n and s ≥ 2 the rule gives p_s = |Q|
--   - encoding: Õ((nk)^{O(K¹⁰)} log(1/δ)) samples and (nk)^{poly(K)} log(1/δ) time; the factor K^{s−1} → C(nk)^{C·K¹⁰}·log(1/δ) samples and C(nk)^{C·K^C}·log(1/δ) work with one natural number C; K^s/K; reason: explicit constants, logarithmic factors absorbed by the exponent since nk ≥ 4; K^s/K = K^{s−1} for K > 0 and avoids a truncated subtraction
--   - encoding: a set R̂ ⊆ ℝⁿ of recovered regressors with a bijection match : R̂ → R ⊊ [k] → estimates indexed by positions 1, …, m with m < k and an injective index map; the program receives m and the estimates, not the matching; reason: same instances (accurate estimates of distinct regressors are distinct); the order of the list carries no information about the matching
--   - encoding: s := K⁴ log n (Hyperparameters 4.1), used as a tensor order → s = ⌈K⁴ log n⌉ (the published hypS); reason: the convention of the published base mission; (182) states s ≤ 2K⁴ log n
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 6.3, p.30 (PDF p.33); Algorithm 6.1, p.34 (PDF p.37)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_sampleLaw
import Definitions.Def_SelfSelReg_ArithmeticCoin
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_restrictedMoment
import Definitions.Def_SelfSelReg_Supplement_RecoveredList
import Definitions.Def_SelfSelReg_Supplement_Routine
import Definitions.Def_SelfSelReg_Supplement_ProjectedMoments

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

namespace Supplement

/-- **Theorem 6.3** (Projected-Moment Accuracy).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 6.3, p.30 (PDF p.33); Algorithm 6.1, p.34 (PDF p.37):
"Consider the Gaussian self-selection model (Definition 1.1) under the boundedness and uncoveredness
assumptions (Assumption 1.2), with k ≥ 2 and the hyperparameters from Hyperparameters 4.1. Fix a
recovered list R̂ matched bijectively to R ⊊ [k] such that ‖ŵ − w_match(ŵ)‖₂ ≤ e^{−K⁶s} (ŵ ∈ R̂), and put
Q = [k] ∖ R. For δ ∈ (0, 1/3), run ESTIMATEPROJECTEDMOMENTS (Algorithm 6.1) with sampling accuracy
e^{−K⁶s}, failure probability δ, and fresh observations independent of R̂. With probability at least
1 − δ, the returned matrices Â, M̂_1, …, M̂_n form an e^{−K²s}-estimate of the projected moment matrices
for Q relative to the constructed map C_s (Definition 6.2), and
‖(I − C_sᵀC_s)(A^{(s)}_Q)^{1/2}‖²_op ≤ 2K^{s−1}e^{−K²s} tr(A^{(s)}_Q). Its sample complexity is
Õ((nk)^{O(K¹⁰)} log(1/δ)), and its running time is (nk)^{poly(K)} log(1/δ)."

**Formalization Note.**
* The routine is one program `P` of the published sampling real RAM, restricted by `ArithmeticCoin`,
  chosen with the constant `C` before every parameter and instance, as in the published goal. It runs
  in dimension `n + 1`, receives `k, B, ∆, δ, |R̂|` and the estimates of `R̂`, and reads observations
  `(X, Y_max)` by `sample`. The sampling accuracy `e^{−K⁶s}` is determined by `B, ∆, n` and is not a
  separate input.
* The returned matrices have dimension `p_s = |Q|`: Algorithm 6.1 sets `p_1 = n` and
  `p_{r+1} = min{k − |R̂|, p_r n}`, so `p_r = |Q|` for every `r ≥ 2` (as `|Q| ≤ k ≤ n`), and `s ≥ 2`.
  `Â` is `decodeMat |Q| 0` and `M̂_ℓ` is `decodeMat |Q| ℓ` (`ℓ = 1, …, n`); they are symmetric on
  every run.
* "The constructed map `C_s`" is internal to the run (Algorithm 6.1 returns only `Â, M̂_1, …, M̂_n`):
  on the success event there is a map `C_s` with orthonormal rows for which both displayed
  conclusions hold. `(A^{(s)}_Q)^{1/2}` is the positive semidefinite square root (`ProjectionError`).
* `K^{s−1}` is written `K^s/K` (`K > 0`). Resource bounds as in Theorem 6.1. -/
theorem theorem_6_3 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticCoin P) (C : ℕ),
      ∀ (n k : ℕ), 2 ≤ k → k ≤ n →
      ∀ (B Δ δ : ℝ), 1 ≤ B → 0 < Δ → Δ ≤ 1 → 0 < δ → δ < 1 / 3 →
      ∀ w : Fin k → EuclideanSpace ℝ (Fin n), SatisfiesAssumption B Δ w →
      ∀ Rhat : RecoveredList n k,
        Rhat.Accurate w (Real.exp (-(hypK B Δ ^ 6 * hypS B Δ n))) →
        RandomizedRoutine P
          ([(k : ℝ), B, Δ, δ, (Rhat.size : ℝ)] ++ Rhat.data)
          (sampleLaw w) δ
          (C * ((n : ℝ) * k) ^ ((C : ℝ) * hypK B Δ ^ 10) * Real.log (1 / δ))
          (C * ((n : ℝ) * k) ^ ((C : ℝ) * hypK B Δ ^ C) * Real.log (1 / δ))
          (fun st => (decodeMat Rhat.remaining.card 0 st).IsHermitian ∧
            ∀ l : Fin n, (decodeMat Rhat.remaining.card ((l : ℕ) + 1) st).IsHermitian)
          (fun st => ∃ Cs : Matrix (Fin Rhat.remaining.card) (Fin (hypS B Δ n) → Fin n) ℝ,
            IsProjectedMomentEstimate w (hypT B Δ n) Rhat.remaining Cs
              (decodeMat Rhat.remaining.card 0 st)
              (fun l : Fin n => decodeMat Rhat.remaining.card ((l : ℕ) + 1) st)
              (Real.exp (-(hypK B Δ ^ 2 * hypS B Δ n))) ∧
            ProjectionError Cs (evenTarget w (hypT B Δ n) Rhat.remaining (hypS B Δ n))
              (2 * (hypK B Δ ^ hypS B Δ n / hypK B Δ) * Real.exp (-(hypK B Δ ^ 2 * hypS B Δ n)) *
                Matrix.trace (evenTarget w (hypT B Δ n) Rhat.remaining (hypS B Δ n)))) := by sorry

end Supplement

end SelfSelReg
