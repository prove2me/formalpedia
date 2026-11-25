-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_rho_inv_loc
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.rho_inv_loc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:27.239207+00:00
-- url     : https://prove2.me/theorems/3cf47b78-6bcc-4a30-87c0-69f4554ff4df
-- title:
--   TLin Pf: rho inv loc
-- statement:
--   The TLin Pf construction uses the rho inv loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/CompBaseEq.lean#L60-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/CompBaseEq.lean#L60-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_WchartInlLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ActActA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_CompBaseEq
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
include hO

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.rho_inv_loc
    (hi : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
        (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i)
    (ρ : Γ((thickObj R I e G).left, ⊤)ˣ) (hρ : PairProp U ιD ιG e a χ u ρ)
    (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (jB : Fin 4 → D.toPre.P.L.ι)
    (cA : LB.Coh D.toPre.P.L (φA U ιD e a χ) jA) (cB : LB.Coh D.toPre.P.L (φB U ιG e a χ) jB)
    (cAB : ∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB k = jA k')
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hsV : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB ⊓ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA))
    (ht1 : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ ⊤)
    (ht2 : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ ⊤) :
    ((WeightPf.act (U.gt e)).left.appLE ⊤ W' ht1).hom ρ.val =
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE ⊤ W' ht2).hom ρ.val := by sorry
