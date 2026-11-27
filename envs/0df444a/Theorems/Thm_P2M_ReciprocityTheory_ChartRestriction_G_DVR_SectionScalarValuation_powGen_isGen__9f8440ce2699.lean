-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_powGen_isGen__9f8440ce2699
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_powGen_isGen__9f8440ce2699
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T06:23:11.988577+00:00
-- url     : https://prove2.me/theorems/63ed48ff-0688-5152-b726-0c27b606ed9e
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation pow Gen is Gen  9f8440ce2699: P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation pow Gen is Gen  9f8440ce
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation pow Gen is Gen  9f8440ce2699 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation pow Gen is Gen  9f8440ce2699 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsValGenHasVal.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsValGenHasVal.lean#L17-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsValGenHasVal
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_powGen_isGen__9f8440ce2699 {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) : (GeneratorPullback.powGen L φ ε t n).IsGen := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«SectionScalarValuation».«powGen_isGen'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_powGen_isGen__9f8440ce2699
