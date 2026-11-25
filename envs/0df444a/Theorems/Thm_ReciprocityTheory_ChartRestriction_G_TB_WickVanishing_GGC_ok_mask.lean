-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_ok_mask
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.ok_mask
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:15.128712+00:00
-- url     : https://prove2.me/theorems/500b4e87-9574-4800-aff2-fcf84e5e493d
-- title:
--   GGC: ok mask
-- statement:
--   The GGC construction uses the ok mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L168-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L168-L176

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
variable {p0 : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.ok_mask {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ok p0 (mask p0 t y) := by sorry
