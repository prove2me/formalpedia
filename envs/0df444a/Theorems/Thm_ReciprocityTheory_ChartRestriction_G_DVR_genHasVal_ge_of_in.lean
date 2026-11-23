-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_ge_of_in
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_ge_of_in
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:58.660727+00:00
-- url     : https://prove2.me/theorems/a3fc687c-82a1-4f3a-9fc4-2610fde2aa0a
-- title:
--   DVR: gen Has Val ge of in
-- statement:
--   The DVR construction uses the gen Has Val ge of in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L411-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L411-L482

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_ge_of_in (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (x : Spec (CommRingCat.of V) ⟶ X) (x' : Spec (CommRingCat.of (FractionRing V)) ⟶ X) (hx : x' = jK V ≫ x)
    (ε : ℤ) (t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε))) (k : ℕ)
    (hin : ∀ (j : PUnit → L.ι) (W : (Spec (CommRingCat.of V)).Opens), IsAffineOpen W →
      W ≤ x ⁻¹ᵁ L.U (j PUnit.unit) →
      ∀ h : jK V ⁻¹ᵁ W ≤ (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε)).U j,
        ∃ r ∈ (IsLocalRing.maximalIdeal V ^ k).map (DegPre.toOpen W),
          ((jK V).app W).hom r =
            ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE h).op).hom (t.s j).val)
    {n : ℤ} (hn : GenHasVal ϖ L (fun _ => x) (fun _ => x') (fun _ => hx) (fun _ => ε) t n) : (k : ℤ) ≤ n := by sorry
