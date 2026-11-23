-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_iic_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.iic_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:43.314806+00:00
-- url     : https://prove2.me/theorems/b93b5a5c-de3d-430d-85f1-ee4f9652e0d6
-- title:
--   J2: iic zero
-- statement:
--   The J2 construction uses the iic zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/TailFinOf.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/TailFinOf.lean#L24-L26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailFinOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.iic_zero {n : ℕ} (g : Fin (n + 1) → ℝ) : ∑ j ∈ Finset.Iic 0, g j = g 0 := by sorry
