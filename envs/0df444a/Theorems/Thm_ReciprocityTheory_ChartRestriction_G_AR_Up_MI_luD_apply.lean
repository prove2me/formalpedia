-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_luD_apply
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.luD_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:13.65545+00:00
-- url     : https://prove2.me/theorems/c6af714a-bb05-48a1-8398-2fad12a622ee
-- title:
--   MI: lu D apply
-- statement:
--   The MI construction uses the lu D apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfA.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfA.lean#L86-L89

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.luD_apply (w h : Ix ι r → ℂ) (i : Ix ι r) :
    luD w h i = ∑ k, sl h i.1 i.2.1 k * up w i.1 k i.2.2 + ∑ k, (1 + sl w i.1) i.2.1 k * up h i.1 k i.2.2 := by sorry
