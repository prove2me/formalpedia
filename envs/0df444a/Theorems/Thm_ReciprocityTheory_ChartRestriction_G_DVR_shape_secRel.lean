-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_secRel
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.shape_secRel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:09:58.537896+00:00
-- url     : https://prove2.me/theorems/9b98ba52-211c-44f3-add2-b730dae07653
-- title:
--   DVR: shape sec Rel
-- statement:
--   The DVR construction uses the shape sec Rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullGen.lean#L489-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullGen.lean#L489-L497

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem ReciprocityTheory.ChartRestriction.G.DVR.shape_secRel {Y : Scheme.{0}} {U₁ U₂ U₃ W V₂ O : Y.Opens} (hW : W ≤ U₃) (hWV : W ≤ V₂) (hV : V₂ ≤ U₂)
    (o : O ≤ W ⊓ U₁) (o₁ : O ≤ U₁) (o₂ : O ≤ U₂) (o₃ : O ≤ U₃) (x : Γ(Y, U₁)) (y : Γ(Y, U₂)) (u : Γ(Y, U₃)ˣ)
    (e : rs (inf_le_left : W ⊓ U₁ ≤ W) (rs hW (u : Γ(Y, U₃)) * rs hWV (rs hV y)) =
      rs (inf_le_right : W ⊓ U₁ ≤ U₁) x) :
    rs o₁ x = rs o₂ y * rs o₃ (u : Γ(Y, U₃)) := by sorry
