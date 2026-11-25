-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ofId_ext
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.ofId_ext
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:56:44.807704+00:00
-- url     : https://prove2.me/theorems/363662e8-acd8-4de3-874b-046ea7b3ee60
-- title:
--   Chart: of Id ext
-- statement:
--   The Chart construction uses the of Id ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsAwayNotMem.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsAwayNotMem.lean#L14-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory

theorem ReciprocityTheory.ChartRestriction.G.Chart.ofId_ext {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] (f g : S →ₐ[S] B) : f = g := by sorry
