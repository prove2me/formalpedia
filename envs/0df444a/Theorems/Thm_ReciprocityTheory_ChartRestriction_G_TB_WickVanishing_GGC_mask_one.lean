-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_mask_one
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.mask_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:05.540453+00:00
-- url     : https://prove2.me/theorems/4f56ab5a-d730-5ae5-842a-26fd333a8050
-- title:
--   GGC: mask one
-- statement:
--   The GGC construction uses the mask one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L206-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L206-L208

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.mask_one (y : Matrix (Fin r) (Fin r) ℂ) : mask p0 1 y = y := by sorry
