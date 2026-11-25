-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_cross
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.shape_cross
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:19.070801+00:00
-- url     : https://prove2.me/theorems/284bef3b-2e09-4911-ab7a-bf09f85313bf
-- title:
--   DVR: shape cross
-- statement:
--   The DVR construction uses the shape cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L269-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L269-L310

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {G : Over (Spec (CommRingCat.of V))}

theorem ReciprocityTheory.ChartRestriction.G.DVR.shape_cross {Y Y' : Scheme.{0}} (h : Y' ⟶ Y) (e : Y' ⟶ Y') (fl : Y ⟶ Y) (he : e ≫ h = h ≫ fl)
    (c : Fin 2 → Γ(Y', ⊤)) (hce : ∀ i, e.appTop.hom (c i) = c i)
    {Ua Ub O : Y.Opens} {Sa Sb Wa Wb W : Y'.Opens}
    (oa : O ≤ Ua) (ob : O ≤ fl ⁻¹ᵁ Ub) (hWa : Wa ≤ h ⁻¹ᵁ Ua) (hWa' : Wa ≤ Sa) (hWb : Wb ≤ h ⁻¹ᵁ Ub) (hWb' : Wb ≤ Sb)
    (wO : W ≤ h ⁻¹ᵁ O) (wa : W ≤ Wa) (wSa : W ≤ Sa) (wb : W ≤ e ⁻¹ᵁ Wb) (wSb : W ≤ e ⁻¹ᵁ Sb)
    (hunit : ∀ i, IsUnit (resTop W (c i)))
    (σ : Fin 2 → Γ(Y, Ua)) (τ : Fin 2 → Γ(Y, Ub)) (x : Fin 2 → Γ(Y', Sa)) (y : Fin 2 → Γ(Y', Sb))
    (hC : rs oa (σ 0) * rs ob ((fl.app Ub).hom (τ 1)) = rs oa (σ 1) * rs ob ((fl.app Ub).hom (τ 0)))
    (hσ : ∀ i, rs hWa ((h.app Ua).hom (σ i)) = resTop Wa (c i) * rs hWa' (x i))
    (hτ : ∀ i, rs hWb ((h.app Ub).hom (τ i)) = resTop Wb (c i) * rs hWb' (y i)) :
    rs wSa (x 0) * rs wSb ((e.app Sb).hom (y 1)) = rs wSa (x 1) * rs wSb ((e.app Sb).hom (y 0)) := by sorry
