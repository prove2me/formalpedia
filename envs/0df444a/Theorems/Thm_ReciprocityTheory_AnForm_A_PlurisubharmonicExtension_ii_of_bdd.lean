-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_ii_of_bdd
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.ii_of_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:57.959633+00:00
-- url     : https://prove2.me/theorems/03d040b1-592d-4c6d-b336-e26899498f0a
-- title:
--   Plurisubharmonic Extension: ii of bdd
-- statement:
--   The Plurisubharmonic Extension construction uses the ii of bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtB.lean#L332-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtB.lean#L332-L337

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
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

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.ii_of_bdd {f : ℝ → ℝ} (hf : Measurable f) (B : ℝ) (hB : ∀ θ, |f θ| ≤ B) (a b : ℝ) :
    IntervalIntegrable f volume a b := by sorry
