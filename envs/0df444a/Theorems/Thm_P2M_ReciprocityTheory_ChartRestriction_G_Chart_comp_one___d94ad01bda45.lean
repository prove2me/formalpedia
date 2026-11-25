-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one___d94ad01bda45
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one___d94ad01bda45
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:10.190597+00:00
-- url     : https://prove2.me/theorems/ca3c3750-7b07-5359-80bf-c7253d5ec3f7
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Chart comp one   d94ad01bda45: P2 M Reciprocity Theory Chart Restriction G Chart comp one   d94ad01bda45
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Chart comp one   d94ad01bda45 construction uses the P2 M Reciprocity Theory Chart Restriction G Chart comp one   d94ad01bda45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLie.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLie.lean#L38-L39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [Field k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)
variable {tk g}

theorem P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one___d94ad01bda45 {T : Scheme.{0}} {X Y M : Over T} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Chart».«comp_one''» := P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one___d94ad01bda45
