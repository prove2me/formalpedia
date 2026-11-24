-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWM_vge_moveO
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TWM.vge_moveO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:47.698478+00:00
-- url     : https://prove2.me/theorems/d34e5cfa-1040-4648-a1da-4d96d805a743
-- title:
--   TWM: vge move O
-- statement:
--   The TWM construction uses the vge move O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/TWMove.lean#L64-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/TWMove.lean#L64-L176

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem ReciprocityTheory.ChartRestriction.G.DVR.TWM.vge_moveO (hTW : TwistBCSpanStatement) {k : ℕ} (hk : 1 ≤ k) {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {H : (TO hϖ hv ⊗ D.toPre.P.A).left ⟶ (TO hϖ hv ⊗ D.toPre.P.A).left}
    (hh : h ≫ (jO hϖ hv (D := D)).left = (jO hϖ hv).left ≫ H)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k) s h φ₃ ε₃ u)
    {ψ : K₄ → ((TO hϖ hv ⊗ D.toPre.P.A).left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eO : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heO : eO.IsGen)
    (hform : FormEq (Sum.elim (fun i => (H ≫ (snd (TO hϖ hv) D.toPre.P.A).left) ≫ D.toPre.famφB α i) ψ)
      (Sum.elim (DegPre.famε k) δ) (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB χ i) (DegPre.famε k))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eO (jO hϖ hv).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k α s r) : VGe D F v k χ s' (r + q) := by sorry
