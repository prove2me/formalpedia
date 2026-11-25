-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_comp_pow__ea2edb35d3f7
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_comp_pow__ea2edb35d3f7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:12.091283+00:00
-- url     : https://prove2.me/theorems/de5fc3b9-725e-4c9f-a14d-8a3263f7cd08
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR comp pow  ea2edb35d3f7: P2 M Reciprocity Theory Chart Restriction G DVR comp pow  ea2edb35d3f7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR comp pow  ea2edb35d3f7 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR comp pow  ea2edb35d3f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L226-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L226-L228

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
variable {M : LB A.left}

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_comp_pow__ea2edb35d3f7 (f : T ⟶ A) (g : A ⟶ A) : ∀ n : ℕ, f ≫ g ^ n = (f ≫ g) ^ n
  := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«comp_pow'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_comp_pow__ea2edb35d3f7
