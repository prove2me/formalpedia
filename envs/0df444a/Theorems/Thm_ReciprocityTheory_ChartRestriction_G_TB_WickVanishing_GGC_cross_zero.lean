-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_cross_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.cross_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:15.515495+00:00
-- url     : https://prove2.me/theorems/d5b385fe-a65e-490d-a12c-b1e45f8b7179
-- title:
--   GGC: cross zero
-- statement:
--   The GGC construction uses the cross zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L121-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L121-L135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.cross_zero {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) {a b : Fin r}
    (hab : ¬((a : ℕ) < p0 ↔ (b : ℕ) < p0)) : Gy p0 y a b = 0 := by sorry
