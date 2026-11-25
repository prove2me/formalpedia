-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:54:39.768666+00:00
-- url     : https://prove2.me/theorems/6d555d57-f1be-5cd0-aa34-86bf9a73e2ab
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Chart one left  f4b8b6e904c4: P2 M Reciprocity Theory Chart Restriction G Chart one left  f4b8b6e904c4
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Chart one left  f4b8b6e904c4 construction uses the P2 M Reciprocity Theory Chart Restriction G Chart one left  f4b8b6e904c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLie.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankLie.lean#L34-L36

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4 {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Chart».«one_left'» := P2M_ReciprocityTheory_ChartRestriction_G_Chart_one_left__f4b8b6e904c4
