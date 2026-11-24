-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_bdd
-- name    : ReciprocityTheory.AnForm.A.polyMax_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:05.84156+00:00
-- url     : https://prove2.me/theorems/b72057e3-65ef-41f4-942a-0e06ca4f6695
-- title:
--   A: poly Max bdd
-- statement:
--   The A construction uses the poly Max bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L16-L18

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

theorem ReciprocityTheory.AnForm.A.polyMax_bdd (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (h : closedBall z t ⊆ U) :
    BddAbove (φ '' closedBall z t) := by sorry
