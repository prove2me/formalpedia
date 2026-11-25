-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_contDiffOn_dzb
-- name    : ReciprocityTheory.AnForm.A.contDiffOn_dzb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:14.15942+00:00
-- url     : https://prove2.me/theorems/b57c645a-818b-4209-b419-618ee05fcf5b
-- title:
--   A: cont Diff On dzb
-- statement:
--   The A construction uses the cont Diff On dzb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsIbp.lean#L32-L40

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

theorem ReciprocityTheory.AnForm.A.contDiffOn_dzb {D : ℕ} {f : (Fin D → ℂ) → ℂ} {U : Set (Fin D → ℂ)} {n m : WithTop ℕ∞}
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (hmn : m + 1 ≤ n) (j : Fin D) :
    ContDiffOn ℝ m (dzb j f) U := by sorry
