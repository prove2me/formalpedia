-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_diff_last
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.det_diff_last
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:59.98028+00:00
-- url     : https://prove2.me/theorems/15f1375d-d82d-5a22-b32c-96430cc86cff
-- title:
--   MI: det diff last
-- statement:
--   The MI construction uses the det diff last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfC.lean#L31-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfC.lean#L31-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.det_diff_last {k : ℕ} (B B' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (h : ∀ a b, ¬ (a = Fin.last k ∧ b = Fin.last k) → B a b = B' a b) :
    B.det - B'.det = (B (Fin.last k) (Fin.last k) - B' (Fin.last k) (Fin.last k)) *
      (B.submatrix Fin.castSucc Fin.castSucc).det := by sorry
