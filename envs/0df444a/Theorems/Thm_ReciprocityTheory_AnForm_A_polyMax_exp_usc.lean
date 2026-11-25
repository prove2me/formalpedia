-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_exp_usc
-- name    : ReciprocityTheory.AnForm.A.polyMax_exp_usc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:56.46061+00:00
-- url     : https://prove2.me/theorems/bf2cf9f1-3bb2-5014-91c2-84d103797f6f
-- title:
--   A: poly Max exp usc
-- statement:
--   The A construction uses the poly Max exp usc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L65-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L65-L77

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

theorem ReciprocityTheory.AnForm.A.polyMax_exp_usc (hU : IsOpen U) (hφ : UpperSemicontinuousOn φ U) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall z R ⊆ U) :
    UpperSemicontinuousOn (fun s => polyMax φ z (Real.exp s)) (Iic (Real.log R)) := by sorry
