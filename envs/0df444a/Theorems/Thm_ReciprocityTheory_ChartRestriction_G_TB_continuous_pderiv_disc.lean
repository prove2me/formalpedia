-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_continuous_pderiv_disc
-- name    : ReciprocityTheory.ChartRestriction.G.TB.continuous_pderiv_disc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:19.37594+00:00
-- url     : https://prove2.me/theorems/753da99d-cd7f-4728-a1ec-9c6415829b7d
-- title:
--   TB: continuous pderiv disc
-- statement:
--   The TB construction uses the continuous pderiv disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ContinuousPderivDisc.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ContinuousPderivDisc.lean#L35-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open scoped MvPowerSeries.WithPiTopology

theorem ReciprocityTheory.ChartRestriction.G.TB.continuous_pderiv_disc {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => pderiv R i f) := by sorry
