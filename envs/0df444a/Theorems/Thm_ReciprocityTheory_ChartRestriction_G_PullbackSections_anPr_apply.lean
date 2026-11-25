-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anPr_apply
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.anPr_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:39:21.245573+00:00
-- url     : https://prove2.me/theorems/56fa83cd-d3b4-4895-907d-eb1a7cd06500
-- title:
--   Pullback Sections: an Pr apply
-- statement:
--   The Pullback Sections construction uses the an Pr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L147-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L147-L147

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
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
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y : Scheme.{0}}
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.anPr_apply (i : Fin 2) (v : Fin (2 * g) → ℂ) (j : Fin g) : anPr i v j = v (anKap (i, j)) := by sorry
