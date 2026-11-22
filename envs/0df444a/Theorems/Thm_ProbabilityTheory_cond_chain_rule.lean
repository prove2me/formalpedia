-- Prove2me | Theorems.Thm_ProbabilityTheory_cond_chain_rule
-- name    : ProbabilityTheory.cond_chain_rule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:50.701897+00:00
-- url     : https://prove2.me/theorems/f102a101-bdbc-4ed3-bc69-60a8886cc6a4
-- title:
--   Probability Theory: cond chain rule
-- statement:
--   `H[X, Y | Z] = H[Y | Z] + H[X | Y, Z]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L685-L689
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L685-L689

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

theorem ProbabilityTheory.cond_chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y]
    [FiniteRange Z] :
    H[⟨X, Y⟩ | Z; μ] = H[Y | Z; μ] + H[X | ⟨Y, Z⟩; μ] := by sorry
