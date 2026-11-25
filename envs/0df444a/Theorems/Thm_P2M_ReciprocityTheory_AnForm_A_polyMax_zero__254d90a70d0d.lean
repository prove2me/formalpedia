-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_zero__254d90a70d0d
-- name    : P2M_ReciprocityTheory_AnForm_A_polyMax_zero__254d90a70d0d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:11:45.866819+00:00
-- url     : https://prove2.me/theorems/c37c1435-dc80-4b18-a13d-b606021f68cc
-- title:
--   P2 M Reciprocity Theory An Form A poly Max zero  254d90a70d0d: P2 M Reciprocity Theory An Form A poly Max zero  254d90a70d0d
-- statement:
--   The P2 M Reciprocity Theory An Form A poly Max zero  254d90a70d0d construction uses the P2 M Reciprocity Theory An Form A poly Max zero  254d90a70d0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L40-L41

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

theorem P2M_ReciprocityTheory_AnForm_A_polyMax_zero__254d90a70d0d : polyMax φ z 0 = φ z := by sorry

alias «ReciprocityTheory».«AnForm».«A».«polyMax_zero'» := P2M_ReciprocityTheory_AnForm_A_polyMax_zero__254d90a70d0d
