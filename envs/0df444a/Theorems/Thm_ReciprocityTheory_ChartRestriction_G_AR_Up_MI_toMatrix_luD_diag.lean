-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_toMatrix_luD_diag
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.toMatrix_luD_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:58:13.236555+00:00
-- url     : https://prove2.me/theorems/c69c76d4-56cd-443e-8eed-df849a68c446
-- title:
--   MI: to Matrix lu D diag
-- statement:
--   The MI construction uses the to Matrix lu D diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfA.lean#L121-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfA.lean#L121-L141

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.toMatrix_luD_diag (w : Ix ι r → ℂ) (i : Ix ι r) :
    LinearMap.toMatrix' (luD w) i i = if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by sorry
