-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scale_prodPts
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.scale_prodPts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:17:37.868817+00:00
-- url     : https://prove2.me/theorems/5f3a9630-ad4e-401f-920b-b7639e3aff07
-- title:
--   Chart: scale prod Pts
-- statement:
--   The Chart construction uses the scale prod Pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullbackFactor.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullbackFactor.lean#L28-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
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
variable {R : Type} [CommRing R] {M : Over (Spec (CommRingCat.of R))} [GrpObj M]

theorem ReciprocityTheory.ChartRestriction.G.Chart.scale_prodPts {d : ℕ} (a : R) (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ M)) :
    spMap (scaleD a) ≫ prodPts c v = prodPts (a • c) v := by sorry
