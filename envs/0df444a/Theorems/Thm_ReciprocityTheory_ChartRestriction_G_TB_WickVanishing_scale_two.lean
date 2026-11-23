-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_scale_two
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.scale_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:41:31.10395+00:00
-- url     : https://prove2.me/theorems/4d8b478a-a767-4fc4-ad64-bb32a09f9978
-- title:
--   Wick Vanishing: scale two
-- statement:
--   The Wick Vanishing construction uses the scale two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcAdd.lean#L101-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcAdd.lean#L101-L116

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.scale_two {d : ℕ} (f : PS k 2 d) (c0 c1 : ℕ)
    (h : ev (n := 2) (![fun i => (2 : k) ^ c0 • (X ((0 : Fin 2), i) : PS k 2 d),
      fun i => (2 : k) ^ c1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f = (2 : k) • f)
    (n : Fin 2 × Fin d →₀ ℕ) (hn : c0 * (∑ i, n (0, i)) + c1 * (∑ i, n (1, i)) ≠ 1) : coeff n f = 0 := by sorry
