-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_vanish_first_axis
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:30.313968+00:00
-- url     : https://prove2.me/theorems/75840606-4cba-4f96-9d74-c4262fbe12a2
-- title:
--   Wick Vanishing: coeff eq zero of vanish first axis
-- statement:
--   The Wick Vanishing construction uses the coeff eq zero of vanish first axis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L107-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L107-L116

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0)
    (m : Fin 2 × Fin d →₀ ℕ) (hm : ∀ i, m (0, i) = 0) : coeff m h = 0 := by sorry
