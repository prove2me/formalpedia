-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_dof_addF
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.dof_addF
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:33.862446+00:00
-- url     : https://prove2.me/theorems/cd4f14df-4a4f-408f-a9df-ad77d79d2a0c
-- title:
--   Pullback Sections: dof add F
-- statement:
--   The Pullback Sections construction uses the dof add F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L121-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L121-L132

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.dof_addF {g : ℕ} (v : Fin g → R) (f : PS R 1 g) :
    Dof (addF R g) v f = ∑ j, C (v j) * pderiv R ((0 : Fin 1), j) f := by sorry
