-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_sv_ne
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.sv_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:29.212888+00:00
-- url     : https://prove2.me/theorems/78baba6f-a95d-4556-85e3-bb59c9820b9c
-- title:
--   GGC: sv ne
-- statement:
--   The GGC construction uses the sv ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L113-L119

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.sv_ne {a b : Fin r} (hab : ¬((a : ℕ) < p0 ↔ (b : ℕ) < p0)) : sv p0 b ≠ sv p0 a := by sorry
