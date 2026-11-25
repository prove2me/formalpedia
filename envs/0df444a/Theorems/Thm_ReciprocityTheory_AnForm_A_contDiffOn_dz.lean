-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_contDiffOn_dz
-- name    : ReciprocityTheory.AnForm.A.contDiffOn_dz
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:57.983354+00:00
-- url     : https://prove2.me/theorems/5e7f0c88-7038-4ba7-8711-abd270846795
-- title:
--   A: cont Diff On dz
-- statement:
--   The A construction uses the cont Diff On dz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L22-L30

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.A.contDiffOn_dz {D : ℕ} {f : (Fin D → ℂ) → ℂ} {U : Set (Fin D → ℂ)} {n m : WithTop ℕ∞}
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (hmn : m + 1 ≤ n) (j : Fin D) :
    ContDiffOn ℝ m (dz j f) U := by sorry
