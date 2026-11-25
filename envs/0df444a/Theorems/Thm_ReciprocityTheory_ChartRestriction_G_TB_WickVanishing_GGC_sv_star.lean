-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_sv_star
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.sv_star
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:17.026294+00:00
-- url     : https://prove2.me/theorems/e56177ff-23dd-4a19-a303-b39dc63fc6b1
-- title:
--   GGC: sv star
-- statement:
--   The GGC construction uses the sv star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L76-L78

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.sv_star (a : Fin r) : star (sv p0 a) = sv p0 a := by sorry
