-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_mask_eq
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.mask_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:11.561545+00:00
-- url     : https://prove2.me/theorems/733f3ea6-f696-4b81-a06f-17c0afabd524
-- title:
--   GGC: mask eq
-- statement:
--   The GGC construction uses the mask eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L137-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L137-L164

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.mask_eq {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) (t : ℝ) (s : ℂ) (hs : conj s * s = 1 - (t : ℂ) ^ 2) :
    diagonal (sv p0) * Gy p0 (mask p0 t y) = diagonal (sv p0) * Gy p0 y + (Wm p0 s y)ᴴ * Wm p0 s y := by sorry
