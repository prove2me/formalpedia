-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
-- name    : P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:04.822533+00:00
-- url     : https://prove2.me/theorems/cbf70cfe-bc52-48b9-a4ed-539b371c880b
-- title:
--   P2 M Reciprocity Theory An Form A poly Max le  638c0d78514a: P2 M Reciprocity Theory An Form A poly Max le  638c0d78514a
-- statement:
--   The P2 M Reciprocity Theory An Form A poly Max le  638c0d78514a construction uses the P2 M Reciprocity Theory An Form A poly Max le  638c0d78514a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L24-L26

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}

theorem P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a {t c : ℝ} (ht : 0 ≤ t) (h : ∀ x ∈ closedBall z t, φ x ≤ c) :
    polyMax φ z t ≤ c := by sorry

alias «ReciprocityTheory».«AnForm».«A».«polyMax_le'» := P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
