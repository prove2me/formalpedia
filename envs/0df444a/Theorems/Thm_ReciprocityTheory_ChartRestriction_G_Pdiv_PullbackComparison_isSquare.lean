-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_isSquare
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.isSquare
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:49.616273+00:00
-- url     : https://prove2.me/theorems/210fe8b5-b3e5-5b0c-85af-2652b4169675
-- title:
--   Pullback Comparison: is Square
-- statement:
--   The Pullback Comparison construction uses the is Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L33-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L33-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StSiegPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.isSquare : IsSquare (pφ f G) (pφ₂ f G) := by sorry
