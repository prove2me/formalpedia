-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_one_le_rhoSq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.one_le_rhoSq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:56.024397+00:00
-- url     : https://prove2.me/theorems/c9479ba1-4b76-42b8-aad3-06051c7130d9
-- title:
--   J2: one le rho Sq
-- statement:
--   The J2 construction uses the one le rho Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaugeSplittingAlgebra.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaugeSplittingAlgebra.lean#L48-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.one_le_rhoSq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ rhoSq x l := by sorry
