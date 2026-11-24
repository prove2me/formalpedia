-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_vext_of_mem
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.vext_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:55.52481+00:00
-- url     : https://prove2.me/theorems/1e4e7ce8-6494-4779-b175-3485dbf98903
-- title:
--   Plurisubharmonic Extension: vext of mem
-- statement:
--   The Plurisubharmonic Extension construction uses the vext of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExt.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExt.lean#L54-L57

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
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
open ReciprocityTheory.AnForm.A
variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C κ : ℝ}

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.vext_of_mem {z : Fin D → ℂ} (hz : z ∈ coordDiv S) :
    vext U S u κ z = limsup (trunc u κ) (𝓝[U \ coordDiv S] z) := by sorry
