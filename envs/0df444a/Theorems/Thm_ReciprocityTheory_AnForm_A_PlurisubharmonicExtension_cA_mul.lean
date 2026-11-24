-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_cA_mul
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.cA_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:06.251706+00:00
-- url     : https://prove2.me/theorems/0b773f82-31b6-4037-a967-e971652bd5d0
-- title:
--   Plurisubharmonic Extension: c A mul
-- statement:
--   The Plurisubharmonic Extension construction uses the c A mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtA.lean#L9-L11

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.cA_mul (b : ℝ) (f : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    circleAverage (fun z => b * f z) c R = b * circleAverage f c R := by sorry
