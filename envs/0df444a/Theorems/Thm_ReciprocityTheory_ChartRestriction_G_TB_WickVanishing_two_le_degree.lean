-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_two_le_degree
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.two_le_degree
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:01.402827+00:00
-- url     : https://prove2.me/theorems/b622ba99-0492-4dce-9726-8132fc2daa73
-- title:
--   Wick Vanishing: two le degree
-- statement:
--   The Wick Vanishing construction uses the two le degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L129-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L129-L143

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.two_le_degree {m : Fin 2 × Fin d →₀ ℕ} {i i' : Fin d} (h0 : m (0, i) ≠ 0) (h1 : m (1, i') ≠ 0) :
    2 ≤ m.degree := by sorry
