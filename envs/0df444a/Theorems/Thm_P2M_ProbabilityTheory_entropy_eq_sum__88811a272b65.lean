-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_entropy_eq_sum__88811a272b65
-- name    : P2M_ProbabilityTheory_entropy_eq_sum__88811a272b65
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:03:31.941436+00:00
-- url     : https://prove2.me/theorems/7d294235-b4fe-4a45-8ca1-820e9e912c37
-- title:
--   P2 M Probability Theory entropy eq sum  88811a272b65: P2 M Probability Theory entropy eq sum  88811a272b65
-- statement:
--   The P2 M Probability Theory entropy eq sum  88811a272b65 construction uses the P2 M Probability Theory entropy eq sum  88811a272b65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L125-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L125-L127

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

theorem P2M_ProbabilityTheory_entropy_eq_sum__88811a272b65 (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] :
    entropy X μ = ∑' x, negMulLog ((μ.map X).real {x}) := by sorry

alias «ProbabilityTheory».«entropy_eq_sum'» := P2M_ProbabilityTheory_entropy_eq_sum__88811a272b65
