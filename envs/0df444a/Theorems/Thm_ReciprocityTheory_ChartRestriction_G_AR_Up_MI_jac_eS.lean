-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_jac_eS
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.jac_eS
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:29.613943+00:00
-- url     : https://prove2.me/theorems/349d7460-55dd-56a2-b897-ea796cdf6b93
-- title:
--   MI: jac e S
-- statement:
--   The MI construction uses the jac e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfF.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfF.lean#L71-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.jac_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) : jac ((eS ι r).symm (x, y)) = jacU y := by sorry
