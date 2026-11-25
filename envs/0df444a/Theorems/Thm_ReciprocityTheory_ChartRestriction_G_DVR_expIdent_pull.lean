-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_expIdent_pull
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.expIdent_pull
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:13.108979+00:00
-- url     : https://prove2.me/theorems/1a2551cc-29b3-5b00-b3c5-6b1fb12bb90d
-- title:
--   DVR: exp Ident pull
-- statement:
--   The DVR construction uses the exp Ident pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpIdentRestrict.lean#L130-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpIdentRestrict.lean#L130-L158

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull

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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]

theorem ReciprocityTheory.ChartRestriction.G.DVR.expIdent_pull [DecidableEq D.toPre.X] (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (S : Finset D.toPre.X) (h : ExpIdent U e k σ f S)
    (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
    (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι) (hj : j₁ 0 = p.2 PUnit.unit)
    (hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))))
    {Z : Scheme.{0}} (hh : Z ⟶ (thickObj R I e G).left) {O : Z.Opens}
    (hO : O ≤ hh ⁻¹ᵁ U.expW e p j₁ S jf jt) :
    rs hO ((hh.app _).hom (res (inf_le_left.trans inf_le_left :
        U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
          (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val) ^ k *
      rs hO ((hh.app _).hom (rs (inf_le_left.trans inf_le_right : U.expW e p j₁ S jf jt ≤
        (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)
        (((fstG I e G).left.app _).hom (σ.f j₁)))) =
      ∑ α ∈ S, (if hα : α ∈ S then
        rs hO ((hh.app _).hom (rs (U.expW_le_f e p j₁ jf jt hα)
          (((U.gt e).pG.left.app _).hom ((f α).f (jf α))))) *
        rs hO ((hh.app _).hom (res (U.expWeight_le_chart_weight e p j₁ jf jt hα) (((U.gt e).t α).s (jt α))).val)
        else 0) := by sorry
