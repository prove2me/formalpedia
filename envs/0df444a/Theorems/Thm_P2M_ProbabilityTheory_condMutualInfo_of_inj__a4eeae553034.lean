-- Prove2me | Theorems.Thm_P2M_ProbabilityTheory_condMutualInfo_of_inj__a4eeae553034
-- name    : P2M_ProbabilityTheory_condMutualInfo_of_inj__a4eeae553034
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:07:54.007808+00:00
-- url     : https://prove2.me/theorems/87938a6f-3d99-4125-9f18-f2eb50aa825b
-- title:
--   P2 M Probability Theory cond Mutual Info of inj  a4eeae553034: P2 M Probability Theory cond Mutual Info of inj  a4eeae553034
-- statement:
--   The P2 M Probability Theory cond Mutual Info of inj  a4eeae553034 construction uses the P2 M Probability Theory cond Mutual Info of inj  a4eeae553034 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1077-L1101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/Basic.lean#L1077-L1101

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

theorem P2M_ProbabilityTheory_condMutualInfo_of_inj__a4eeae553034
    {S T U S' T' U' Ω : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U]
    [MeasurableSpace S'] [MeasurableSingletonClass S'] [Countable S']
    [MeasurableSpace T'] [MeasurableSingletonClass T'] [Countable T']
    [MeasurableSpace U'] [MeasurableSingletonClass U'] [Countable U']
    {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    {f : S → S'} (hf : Function.Injective f)
    {g : T → T'} (hg : Function.Injective g)
    {h : U → U'} (hh : Function.Injective h)
    : I[f ∘ X : g ∘ Y | h ∘ Z; μ] = I[X : Y | Z; μ] := by sorry

alias «ProbabilityTheory».«condMutualInfo_of_inj'» := P2M_ProbabilityTheory_condMutualInfo_of_inj__a4eeae553034
