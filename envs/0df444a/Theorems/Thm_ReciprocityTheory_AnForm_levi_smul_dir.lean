-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
-- name    : ReciprocityTheory.AnForm.levi_smul_dir
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:38.133494+00:00
-- url     : https://prove2.me/theorems/54788c61-96b0-4e0f-9dc5-0d7e1d83274d
-- title:
--   An Form: levi smul dir
-- statement:
--   The An Form construction uses the levi smul dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PshShiftA.lean#L72-L77

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

theorem ReciprocityTheory.AnForm.levi_smul_dir (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) (t : ℝ) :
    levi φ z (t • w) = t ^ 2 * levi φ z w := by sorry
