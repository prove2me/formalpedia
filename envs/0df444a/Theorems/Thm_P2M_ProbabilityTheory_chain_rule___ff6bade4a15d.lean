-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_chain_rule___ff6bade4a15d
-- name    : P2M_ProbabilityTheory_chain_rule___ff6bade4a15d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:51:24.728088+00:00
-- url     : https://prove2.me/theorems/8793e0a9-6d8c-46fa-873a-88191917b27f
-- title:
--   P2 M Probability Theory chain rule   ff6bade4a15d: P2 M Probability Theory chain rule   ff6bade4a15d
-- statement:
--   Another form of the chain rule : `H[X | Y] = H[X, Y] - H[Y]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L626-L629
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L626-L629

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
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]

theorem P2M_ProbabilityTheory_chain_rule___ff6bade4a15d (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[X | Y; μ] = H[⟨X, Y⟩; μ] - H[Y; μ] := by sorry

alias «ProbabilityTheory».«chain_rule''» := P2M_ProbabilityTheory_chain_rule___ff6bade4a15d
