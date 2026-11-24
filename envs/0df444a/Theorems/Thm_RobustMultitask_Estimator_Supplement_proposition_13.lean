-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_Supplement_proposition_13
-- name    : RobustMultitask.Estimator.Supplement.proposition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:05:47.404283+00:00
-- url     : https://prove2.me/theorems/685abfbe-3be4-401b-a78a-d46f541f6244
-- title:
--   Proposition 13, p. 67 (corrected: instance-specific λ₀, d ≥ 2) — data-poor forced-sample tail bound 13/T
-- statement:
--   Work in the bandit model of §5 under Assumptions 6–10, with $C_0>2$, $d\ge2$, $s\ge1$ and total horizon $H\ge1$. Let $j$ be the data-poor instance and run the data-poor RMBandit (instance $j$ omitted from every shared trimmed mean) with the hyperparameters and $q$ of Appendix D.2, $|\mathcal B_0|=\lceil q\log H\rceil$, and any selection and tie-breaking rules. Assume
--   $$\eta_0=\sqrt{\frac{27\log(d)|\mathcal B_0|}{qN}}\le\frac12-\frac1{C_0}-\frac{C_0-2}{4C_0}.$$
--   Then for every arm $k$,
--   $$\mathbb P\Bigl[\|\widehat\beta^j_{k,0}-\beta^j_k\|_1\ge\frac h{4x_{\max}}\Bigr]\le\frac{13}H .$$
--
--   The forced-sample estimator of the data-poor instance is accurate after only $O(\log H)$ forced steps although the instance's design is high-dimensional, because its estimator needs only a compatibility condition on its own samples.
--
--   **Formalization Note** $H$ is the total horizon. The probability is an outer measure.
--
--   Differences from the source:
--   - correction: λ₀ = maxᵢ √(96σᵢ² x²_max K log(d)|ℬ₀|/q) (D.2 display) → instance-specific λ₀^{(j)}; reason: the proof (p. 68) sets λⱼ = √(96σⱼ² x²_max K log(d)|ℬ₀|/(q|ℬʲ₀|)) and matches q's first term σⱼ²s²/pⱼ
--   - correction: no condition on d → d ≥ 2; reason: as in Proposition 11; excluded: d = 1
--   - reading: N = Ω(log(d) log(T)), with log(T) ≤ ((C₀−2)/(4C₀))²(N−1)/(27 log d) on p. 68 → η₀ ≤ 1/2 − 1/C₀ − ζ₀; reason: this is the requirement the proof states (p. 68); the printed sufficient condition uses N − 1 while η₀ uses N, and the requirement itself is kept
--   - reading: ℬ₀ = [q log(T)] → |ℬ₀| = ⌈q log H⌉; reason: as in Proposition 11
--   - encoding: s ∈ ℕ, an arbitrary minimizer → s ≥ 1, arbitrary non-anticipating selection rules, H ≥ 1; reason: as in Proposition 11
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 67, Proposition 13; parameters p. 67 (Appendix D.2); proof pp. 67–68

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

/-- Proposition 13, p. 67 (proof pp. 67–68), with the hyperparameters and `q` of Appendix D.2.
Under the bandit model and Assumptions 6–10, for `C₀ > 2`, `d ≥ 2`, `s ≥ 1`, total horizon
`H ≥ 1`, and the forced-stage admissibility `η₀ ≤ 1/2 − 1/C₀ − ζ₀` with `ζ₀ = (C₀−2)/(4C₀)` (the
explicit form of `N = Ω(log d log T)`), the forced-sample estimator of the data-poor instance `j`
computed by the data-poor RMBandit (instance `j` omitted from the shared trimmed means) satisfies,
for every arm `k`, `P(‖β̂ʲ_{k,0} − βʲ_k‖₁ ≥ h/(4x_max)) ≤ 13/H`. -/
theorem proposition_13
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
    (j : Fin N)
    (hadm : eta0 N d (poorTuning K d s σ p C₀ xmax h pstar ψ ρ j H).b0
        (qPoor K d s σ p C₀ xmax h pstar ψ j) ≤ 1 / 2 - 1 / C₀ - (C₀ - 2) / (4 * C₀))
    (k : Fin K) :
    P {ω | h / (4 * xmax) ≤ l1 (forcedEstimate sel tb
        (poorTuning K d s σ p C₀ xmax h pstar ψ ρ j H) β Z Xc ε ω j k - β j k)}
      ≤ ENNReal.ofReal (13 / H) := by sorry

end RobustMultitask.Estimator.Supplement
