-- Prove2me | Theorems.Thm_ProbabilityTheory_iIndepFun_entropy_eq_add
-- name    : ProbabilityTheory.iIndepFun.entropy_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:42.823859+00:00
-- url     : https://prove2.me/theorems/23aa8e10-09de-4bb1-bdf6-15c55718934b
-- title:
--   i Indep Fun: entropy eq add
-- statement:
--   The i Indep Fun construction uses the entropy eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L844-L887
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L844-L887

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

theorem ProbabilityTheory.iIndepFun.entropy_eq_add {Ω S : Type*} [hΩ:
  MeasureSpace Ω] [IsProbabilityMeasure hΩ.volume]
    {m : ℕ} [MeasurableSpace S] [MeasurableSingletonClass S] [Finite S]
    {X : Fin m → Ω → S} (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X) :
    H[(fun ω i ↦ X i ω)] = ∑ i, H[X i] := by sorry
