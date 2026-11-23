-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_exp_cut
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GE.exp_cut
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:14.440397+00:00
-- url     : https://prove2.me/theorems/3013eb44-714b-4343-baf2-827189c9bb4e
-- title:
--   GE: exp cut
-- statement:
--   The GE construction uses the exp cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L246-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L246-L292

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable [Algebra ℚ k]

theorem ReciprocityTheory.ChartRestriction.G.TB.GE.exp_cut (t : k) (q : PS k 1 d) (hq0 : constantCoeff q = 0) (N : ℕ) :
    ∃ Y : PS k 1 d, FB.expS k (t • q) =
      ∑ n ∈ Finset.range (N + 1), C (algebraMap ℚ k (1 / (n.factorial : ℚ)) * t ^ n) * q ^ n +
        q ^ (N + 1) * Y := by sorry
