-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cons_symm
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.cons_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:57.207637+00:00
-- url     : https://prove2.me/theorems/75495aec-862d-4bec-8944-48abefb2822d
-- title:
--   J2: cons symm
-- statement:
--   The J2 construction uses the cons symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L93-L99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.cons_symm {p : ℕ} (q : ℂ × (Fin p → ℂ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm q = Fin.cons q.1 q.2 := by sorry
