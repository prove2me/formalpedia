-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_contDiff_insertNth_pair
-- name    : ReciprocityTheory.AnForm.A.contDiff_insertNth_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:43.989949+00:00
-- url     : https://prove2.me/theorems/84fc4ca0-5c29-4683-85bb-a2b403c55fbd
-- title:
--   A: cont Diff insert Nth pair
-- statement:
--   The A construction uses the cont Diff insert Nth pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L58-L71

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section

theorem ReciprocityTheory.AnForm.A.contDiff_insertNth_pair {D : ℕ} (j : Fin (D + 1)) :
    ContDiff ℝ 2 (fun q : ℂ × (Fin D → ℂ) => (Fin.insertNth j q.1 q.2 : Fin (D + 1) → ℂ)) := by sorry
