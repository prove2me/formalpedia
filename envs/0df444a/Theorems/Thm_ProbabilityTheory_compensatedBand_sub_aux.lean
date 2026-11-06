-- Prove2me | Theorems.Thm_ProbabilityTheory_compensatedBand_sub_aux
-- name    : ProbabilityTheory.compensatedBand_sub_aux
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:26:45.795352+00:00
-- url     : https://prove2.me/theorems/cd3aa8ad-f6b8-4abb-bd37-a0f7e9aed15c
-- title:
--   LeanLevy: compensated Poisson band integral subtraction
-- statement:
--   The compensated band integral on (0,t] minus the integral on (0,s] is the integral on (s,t], for nonnegative s ≤ t.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L359

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

theorem ProbabilityTheory.compensatedBand_sub_aux
    {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
    {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
    {μ : Measure Ω} {A : Set ℝ} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) :
    compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 t).toLp _)
        - compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 s).toLp _)
      = compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin s t).toLp _) := by sorry
