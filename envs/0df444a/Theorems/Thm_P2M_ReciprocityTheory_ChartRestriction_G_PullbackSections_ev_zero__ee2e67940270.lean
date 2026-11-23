-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_ev_zero__ee2e67940270
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_ev_zero__ee2e67940270
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:18.677523+00:00
-- url     : https://prove2.me/theorems/1535ee57-1c66-457e-88a0-9f321f3ff8f9
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pullback Sections ev zero  ee2e67940270: P2 M Reciprocity Theory Chart Restriction G Pullback Sections ev zero  ee2e67940270
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pullback Sections ev zero  ee2e67940270 construction uses the P2 M Reciprocity Theory Chart Restriction G Pullback Sections ev zero  ee2e67940270 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L114-L119

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable (R : Type) [CommRing R]
variable {R}

theorem P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_ev_zero__ee2e67940270 {m n d : ℕ} (a : Fin m → Pt R n d) : ev a (0 : PS R m d) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«PullbackSections».«ev_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_ev_zero__ee2e67940270
