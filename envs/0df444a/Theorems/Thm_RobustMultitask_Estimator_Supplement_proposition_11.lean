-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_Supplement_proposition_11
-- name    : RobustMultitask.Estimator.Supplement.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:01:57.830824+00:00
-- url     : https://prove2.me/theorems/49f2ac61-787b-4228-b0c0-680778bcbf62
-- title:
--   Proposition 11, p. 55 (corrected: instance-specific λ₀, d ≥ 2) — forced-sample tail bound 8/T of RMBandit
-- statement:
--   Work in the bandit model of §5 under Assumptions 6–10, with $C_0>2$, $d\ge2$, $s\ge1$ and total horizon $H\ge1$. Run RMBandit with the hyperparameters and $q$ of Appendix D.1, so $|\mathcal B_0|=\lceil q\log H\rceil$, and with any LASSO selection rule and any tie-breaking rule. Assume the admissibility condition
--   $$\eta_0=\sqrt{\frac{27\log(d)|\mathcal B_0|}{qN}}\ \le\ \frac12-\frac1{C_0}-\zeta_0,$$
--   the explicit form (41) of $N=\Omega(\log d\log T)$. Then for every instance $j$ and arm $k$,
--   $$\mathbb P\Bigl[\|\widehat\beta^j_{k,0}-\beta^j_k\|_1\ge\frac h{4x_{\max}}\Bigr]\le\frac8H .$$
--
--   The forced-sample estimators are accurate enough to screen out the suboptimal arms; by a union bound the event $\mathcal A$ of (35) fails with probability at most $8KN/H$.
--
--   **Formalization Note** $H$ is the total horizon, the source's $T$ in Appendix D. The probability is an outer measure, so the estimator need not be measurable.
--
--   Differences from the source:
--   - correction: λ₀ = maxᵢ √(96σᵢ² x²_max K log(d)|ℬ₀|/q) (D.1 display) → the instance-specific λ₀^{(j)} = √(96σⱼ² x²_max K log(d)|ℬ₀|/q); reason: the proof (p. 59) sets λⱼ = √(96σⱼ² x²_max K log(d)|ℬ₀|/(q|ℬʲ₀|)), and its error term 768C₀σⱼx_max/((C₀−2)p*ψ)·√(3Ksd log(d)/(qpⱼ)) is matched to q only with σⱼ; with the maximum, q would have to dominate σ̄²/pⱼ, which its first term does not
--   - correction: no condition on d → d ≥ 2; reason: the proof uses (39), 3 log(T) log(x) ≥ log(Tx), with x = d, valid for x > 1, and the source assumes d > 1 (p. 66); at d = 1 the prescribed η₀ and λ₀ vanish and the trimmed-mean tail 3d exp(−Nη₀²/9) = 3 gives no control; excluded: d = 1
--   - reading: N = Ω(log(d) log(T)) → η₀ ≤ 1/2 − 1/C₀ − ζ₀; reason: this is the requirement the proof states (p. 60), of which (41) is the form with |ℬ₀| = q log T; with the rounded |ℬ₀| the requirement itself is kept
--   - reading: ℬ₀ = [q log(T)] → ℬ₀ = {1, …, ⌈q log H⌉}, not intersected with [H] (as printed; only ℬ_m, m ≥ 1, are); reason: the proof uses |ℬ₀| ≥ q log T in the tail bounds, which rounding up preserves
--   - reading: ζ₀ = ((C₀−2)/(4C₀))√(s/d) → with min(s,d) in place of s, and s ≥ 1; reason: as in Theorem 1; the formulas agree when 1 ≤ s ≤ d
--   - encoding: the forced estimator for an arbitrary minimizer → produced by an arbitrary non-anticipating LASSO selection rule; reason: Algorithm 2 computes the estimator from its data only; every selection rule is covered
--   - encoding: no condition on T → H ≥ 1; reason: at H = 0 the bound 8/H is undefined
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 55, Proposition 11; parameters p. 56 (Appendix D.1); proof pp. 58–60, (38)–(41)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Supplement_DataPoor
import Definitions.Def_RobustMultitask_Estimator_Supplement_BanditModel
import Definitions.Def_RobustMultitask_Estimator_Supplement_BanditAlgorithm
import Definitions.Def_RobustMultitask_Estimator_Supplement_BanditTuning

namespace RobustMultitask.Estimator.Supplement

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Proposition 11, p. 55 (proof pp. 56–60), with the hyperparameters and `q` of Appendix D.1.
Under the bandit model and Assumptions 6–10, for `C₀ > 2`, `d ≥ 2`, `s ≥ 1`, total horizon
`H ≥ 1`, and the forced-stage admissibility `η₀ ≤ 1/2 − 1/C₀ − ζ₀` (the explicit form (41) of
`N = Ω(log d log T)`), the forced-sample estimator of every instance `j` and arm `k` computed by
RMBandit (for any LASSO selection and tie-breaking rules) satisfies
`P(‖β̂ʲ_{k,0} − βʲ_k‖₁ ≥ h/(4x_max)) ≤ 8/H`. -/
theorem proposition_11
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N K d : ℕ} [NeZero K] (p : Fin N → ℝ) (PX : Fin N → Measure (Fin d → ℝ))
    (β : Fin N → Fin K → Fin d → ℝ) (βdag : Fin K → Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (Z : ℕ → Ω → Fin N) (Xc : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ)
    (hmodel : IsBanditModel P p PX β βdag s σ Z Xc ε)
    (Kopt : Fin N → Finset (Fin K)) (xmax b h pstar ψ L ρ : ℝ)
    (hA : BanditAssumptions PX β Kopt xmax b h pstar ψ L ρ)
    (C₀ : ℝ) (hC₀ : 2 < C₀) (hd : 2 ≤ d) (hs : 1 ≤ s) (H : ℕ) (hH : 1 ≤ H)
    (sel : LassoSelector d) (tb : ArgmaxRule K) (hsel : IsLassoSelector sel)
    (htb : IsArgmaxRule tb)
    (hadm : eta0 N d (stdTuning K d s σ p C₀ xmax h pstar ψ ρ H).b0
        (qStd K d s σ p C₀ xmax h pstar ψ) ≤ 1 / 2 - 1 / C₀ - zeta0Std d s C₀)
    (j : Fin N) (k : Fin K) :
    P {ω | h / (4 * xmax) ≤ l1 (forcedEstimate sel tb (stdTuning K d s σ p C₀ xmax h pstar ψ ρ H)
        β Z Xc ε ω j k - β j k)}
      ≤ ENNReal.ofReal (8 / H) := by sorry

end RobustMultitask.Estimator.Supplement
