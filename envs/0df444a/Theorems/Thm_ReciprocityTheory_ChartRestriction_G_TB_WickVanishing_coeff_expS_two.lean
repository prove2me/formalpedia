-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_expS_two
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_expS_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:47.223798+00:00
-- url     : https://prove2.me/theorems/877c6f93-d5db-4b6d-8d48-9345537c3e16
-- title:
--   Wick Vanishing: coeff exp S two
-- statement:
--   The Wick Vanishing construction uses the coeff exp S two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L223-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L223-L240

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
variable [Algebra ℚ k]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_expS_two {n : ℕ} (f : PS k n d) (hf : ∀ m : Fin n × Fin d →₀ ℕ, m.degree < 2 → coeff m f = 0)
    (m : Fin n × Fin d →₀ ℕ) (hm : m.degree = 2) : coeff m (FB.expS k f) = coeff m f := by sorry
