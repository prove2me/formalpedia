-- Prove2me | Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
-- name    : P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:17.76312+00:00
-- url     : https://prove2.me/theorems/c18eb2b6-9490-4475-bd23-cc8d6fdde233
-- title:
--   P2 M Measure Theory Measure dirac real apply  5ab26a8900c7: P2 M Measure Theory Measure dirac real apply  5ab26a8900c7
-- statement:
--   The P2 M Measure Theory Measure dirac real apply  5ab26a8900c7 construction uses the P2 M Measure Theory Measure dirac real apply  5ab26a8900c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Dirac.lean#L24-L25
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Dirac.lean#L24-L25

module
public import Mathlib.MeasureTheory.Measure.Dirac
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Dirac
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}

theorem P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7 (a : α) (hs : MeasurableSet s) : (dirac a).real s = s.indicator 1 a := by sorry

alias «MeasureTheory».«Measure».«dirac_real_apply'» := P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
