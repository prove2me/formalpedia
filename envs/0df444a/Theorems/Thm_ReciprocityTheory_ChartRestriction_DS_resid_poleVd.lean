-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_resid_poleVd
-- name    : ReciprocityTheory.ChartRestriction.DS.resid_poleVd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:48.547472+00:00
-- url     : https://prove2.me/theorems/a9ff38f7-b8b8-5144-ba92-8aed71f0e585
-- title:
--   DS: resid pole Vd
-- statement:
--   The DS construction uses the resid pole Vd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L152-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L152-L157

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.resid_poleVd (μ : Fin n → ℝ) (s : Fin n) : resid (poleVd μ) s = ((ratioVd μ s : ℝ) : ℂ) := by sorry
