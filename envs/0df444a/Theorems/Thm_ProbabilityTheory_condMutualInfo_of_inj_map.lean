-- Prove2me | Theorems.Thm_ProbabilityTheory_condMutualInfo_of_inj_map
-- name    : ProbabilityTheory.condMutualInfo_of_inj_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:29.520425+00:00
-- url     : https://prove2.me/theorems/60119402-1e27-445e-80ba-9a0cd9f7d0df
-- title:
--   Probability Theory: cond Mutual Info of inj map
-- statement:
--   If `f(Z, X)` is injective for each fixed `Z`, then `I[f(Z, X) : Y| Z] = I[X : Y| Z]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1048-L1062
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1048-L1062

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
variable [MeasurableSingletonClass U]

theorem ProbabilityTheory.condMutualInfo_of_inj_map
    [Countable U] [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (f : U → S → V) (hf : ∀ t, Function.Injective (f t)) [FiniteRange Z] :
    I[fun ω ↦ f (Z ω) (X ω) : Y | Z; μ] =
    I[X : Y | Z; μ] := by sorry
