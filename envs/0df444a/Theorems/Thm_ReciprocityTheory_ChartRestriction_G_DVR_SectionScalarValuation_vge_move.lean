-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_vge_move
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.vge_move
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:27:37.906427+00:00
-- url     : https://prove2.me/theorems/6c37c262-c84b-46a1-b4bf-cd3653842bf2
-- title:
--   Section Scalar Valuation: vge move
-- statement:
--   The Section Scalar Valuation construction uses the vge move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/SectionScalarValuation.lean#L137-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/SectionScalarValuation.lean#L137-L218

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.vge_move {k : ℕ} {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {TB : D.toPre.P.A.left ⟶ D.toPre.P.A.left}
    (hh : h ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ TB)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k) s h φ₃ ε₃ u)
    {ψ : K₄ → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heB : eB.IsGen)
    (hform : FormEq (Sum.elim (fun i => TB ≫ D.toPre.famφB α i) ψ) (Sum.elim (DegPre.famε k) δ)
      (D.toPre.famφB χ) (DegPre.famε k))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eB (DegPre.prB D.toPre F).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k α s r) : VGe D F v k χ s' (r + q) := by sorry
