-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_usc
-- name    : ReciprocityTheory.AnForm.A.polyMax_usc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:16.16366+00:00
-- url     : https://prove2.me/theorems/349b4a59-c3e9-42df-a3ce-ab21569ea460
-- title:
--   A: poly Max usc
-- statement:
--   The A construction uses the poly Max usc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L43-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L43-L63

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

theorem ReciprocityTheory.AnForm.A.polyMax_usc (hU : IsOpen U) (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (ht : 0 ≤ t)
    (h : closedBall z t ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, closedBall z (t + δ) ⊆ U ∧
      ∀ t', 0 ≤ t' → t' ≤ t + δ → polyMax φ z t' < polyMax φ z t + ε := by sorry
