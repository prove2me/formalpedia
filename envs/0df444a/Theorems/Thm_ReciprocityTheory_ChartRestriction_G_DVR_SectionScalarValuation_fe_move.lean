-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_fe_move
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.fe_move
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T06:26:18.694252+00:00
-- url     : https://prove2.me/theorems/733d3820-ea75-5b17-a055-81e6c56c5af6
-- title:
--   Section Scalar Valuation: fe move
-- statement:
--   The Section Scalar Valuation construction uses the fe move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GsScalJFK.lean#L62-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GsScalJFK.lean#L62-L130

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsValGenHasVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GsScalJFK
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
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.fe_move (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) (k : ℕ)
    (mu α : D.toPre.X) (s : Fam D.toPre F k) {r : ℚ} (hs : VGe D F v k α (s.s α) r) :
    VGe D F v k (α + k • mu) (s.s (α + k • mu)) (r + ((k * Q mu + bOf D.toPre Q mu α : ℤ) : ℚ)) := by sorry
