-- Prove2me | Theorems.Thm_ProbabilityTheory_IndepFun_measureReal_inter_preimage_eq_mul
-- name    : ProbabilityTheory.IndepFun.measureReal_inter_preimage_eq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:51.914407+00:00
-- url     : https://prove2.me/theorems/0171fc97-f27a-4d37-917d-d5cc86563092
-- title:
--   Indep Fun: measure Real inter preimage eq mul
-- statement:
--   The Indep Fun construction uses the measure Real inter preimage eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L29-L34
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/Independence/Basic.lean#L29-L34

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {Ω ι β β' γ : Type*} {κ : ι
  → Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β}
  {g : Ω → β'}

theorem ProbabilityTheory.IndepFun.measureReal_inter_preimage_eq_mul
    {_mβ : MeasurableSpace β}
    {_mβ' : MeasurableSpace β'} (h : IndepFun f g μ) {s : Set β} {t : Set β'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ.real (f ⁻¹' s ∩ g ⁻¹' t) = μ.real (f ⁻¹' s) * μ.real (g ⁻¹' t) := by sorry
