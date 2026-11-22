-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_mutualInfo_eq_entropy_sub_condEntropy__219a0bee1bfe
-- name    : P2M_ProbabilityTheory_mutualInfo_eq_entropy_sub_condEntropy__219a0bee1bfe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:24.768652+00:00
-- url     : https://prove2.me/theorems/566e4e9d-56aa-43f2-adb4-fc64f6ca2949
-- title:
--   P2 M Probability Theory mutual Info eq entropy sub cond Entropy  219a0bee1bfe: P2 M Probability Theory mutual Info eq entropy sub cond Entropy  219a0bee1bfe
-- statement:
--   `I[X : Y] = H[Y] - H[Y | X]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L906-L911
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L906-L911

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
variable [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
variable [Countable S] [Countable T]

theorem P2M_ProbabilityTheory_mutualInfo_eq_entropy_sub_condEntropy__219a0bee1bfe
    (hX : Measurable X) (hY : Measurable Y) (μ :
  Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y; μ] = H[Y; μ] - H[Y | X; μ] := by sorry

alias «ProbabilityTheory».«mutualInfo_eq_entropy_sub_condEntropy'» := P2M_ProbabilityTheory_mutualInfo_eq_entropy_sub_condEntropy__219a0bee1bfe
