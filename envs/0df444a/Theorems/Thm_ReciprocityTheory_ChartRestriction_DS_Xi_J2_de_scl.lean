-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_de_scl
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.de_scl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:22.48599+00:00
-- url     : https://prove2.me/theorems/aeb921bd-40d7-4484-babd-c2a4739d826d
-- title:
--   J2: de scl
-- statement:
--   The J2 construction uses the de scl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaugeSplittingAlgebra.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaugeSplittingAlgebra.lean#L120-L129

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.de_scl {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    de (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * de x i := by sorry
