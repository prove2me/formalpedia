-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_hformF__9b6f59f99d80
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_hformF__9b6f59f99d80
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:27.568731+00:00
-- url     : https://prove2.me/theorems/fdd12c98-6881-5cd0-878c-df0a5823e1ba
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR UUA hform F  9b6f59f99d80: P2 M Reciprocity Theory Chart Restriction G DVR UUA hform F  9b6f59f99d80
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR UUA hform F  9b6f59f99d80 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR UUA hform F  9b6f59f99d80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ChartOfPoint.lean#L67-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ChartOfPoint.lean#L67-L89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ChartOfPoint
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_hformF__9b6f59f99d80 (k : ℕ) (ρ : D.toPre.X) :
    FormEq (DegPre.famφ D.toPre F ρ) (DegPre.famε k)
      (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) (DegPre.famε k) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«UUA».«hformF'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_hformF__9b6f59f99d80
