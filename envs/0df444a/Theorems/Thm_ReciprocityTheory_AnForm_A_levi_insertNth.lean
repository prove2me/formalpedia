-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_levi_insertNth
-- name    : ReciprocityTheory.AnForm.A.levi_insertNth
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:06:01.883293+00:00
-- url     : https://prove2.me/theorems/b70cf820-afbc-49c3-a3a4-e154634ef3fc
-- title:
--   A: levi insert Nth
-- statement:
--   The A construction uses the levi insert Nth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L20-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean#L20-L53

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

theorem ReciprocityTheory.AnForm.A.levi_insertNth {D : ℕ} (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ)
    (hu : ContDiff ℝ 2 u) (w : Fin D → ℂ) (ζ : ℂ) :
    ReciprocityTheory.AnForm.levi u (Fin.insertNth j ζ w) (Pi.single j 1) =
      Δ (fun ζ' => u (Fin.insertNth j ζ' w)) ζ / 4 := by sorry
