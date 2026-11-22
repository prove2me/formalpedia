-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_cond_chain_rule__11c12758197b
-- name    : P2M_ProbabilityTheory_cond_chain_rule__11c12758197b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:45.954849+00:00
-- url     : https://prove2.me/theorems/d76b8a02-1e8a-4cf6-95a8-60abcf4e38fa
-- title:
--   P2 M Probability Theory cond chain rule  11c12758197b: P2 M Probability Theory cond chain rule  11c12758197b
-- statement:
--   If `X : Ω → S`, `Y : Ω → T`, `Z : Ω → U` are random variables,
--   then `H[X, Y | Z] = H[X | Z] + H[Y|X, Z]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L668-L682
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L668-L682

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
variable [Countable U] [MeasurableSingletonClass U]

theorem P2M_ProbabilityTheory_cond_chain_rule__11c12758197b (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[⟨X, Y⟩ | Z; μ] = H[X | Z; μ] + H[Y | ⟨X, Z⟩; μ] := by sorry

alias «ProbabilityTheory».«cond_chain_rule'» := P2M_ProbabilityTheory_cond_chain_rule__11c12758197b
