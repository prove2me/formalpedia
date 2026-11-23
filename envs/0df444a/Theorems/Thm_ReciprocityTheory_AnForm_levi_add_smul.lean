-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
-- name    : ReciprocityTheory.AnForm.levi_add_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:05.782953+00:00
-- url     : https://prove2.me/theorems/04776425-9ddf-43e0-97b3-865718c45b89
-- title:
--   An Form: levi add smul
-- statement:
--   The An Form construction uses the levi add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L79-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L79-L100

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem ReciprocityTheory.AnForm.levi_add_smul {f g : (ι → ℂ) → ℝ} {z : ι → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (w : ι → ℂ) :
    levi (fun y => f y + c * g y) z w = levi f z w + c * levi g z w := by sorry
