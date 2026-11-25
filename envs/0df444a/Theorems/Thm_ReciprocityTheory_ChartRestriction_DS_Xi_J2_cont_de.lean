-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_de
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.cont_de
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:55.762802+00:00
-- url     : https://prove2.me/theorems/98ac65fa-3999-4d87-81fd-f23fb1455153
-- title:
--   J2: cont de
-- statement:
--   The J2 construction uses the cont de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaugeSplittingAlgebra.lean#L145-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaugeSplittingAlgebra.lean#L145-L146

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.cont_de {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => de x l := by sorry
