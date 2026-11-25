-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fp_chart
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.fp_chart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:20.377154+00:00
-- url     : https://prove2.me/theorems/d00c60ef-9d9a-461d-8943-dc217c3b2a81
-- title:
--   Chart: fp chart
-- statement:
--   The Chart construction uses the fp chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L59-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
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
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
variable [∀ s : S, Smooth (Gs G s).hom]
include G

theorem ReciprocityTheory.ChartRestriction.G.Chart.fp_chart {s : S} (C : Chart (Gs G s)) : Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U) := by sorry
