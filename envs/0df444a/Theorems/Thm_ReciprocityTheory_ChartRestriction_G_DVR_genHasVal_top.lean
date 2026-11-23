-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_top
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:15.817448+00:00
-- url     : https://prove2.me/theorems/c66d8cc5-b127-40fd-ac55-7393e48899a3
-- title:
--   DVR: gen Has Val top
-- statement:
--   The DVR construction uses the gen Has Val top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L201-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L201-L236

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
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
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_top {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L (fun k => jK V ≫ φ k) ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ (fun k => jK V ≫ φ k) (fun _ => rfl) ε t n) (j₀ : Ix → L.ι)
    (htop : LB.wchart L φ j₀ = ⊤) (hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ k) j₀) :
    ∃ c : FractionRing V, HasVal ϖ c n ∧ ∃ eV : Vˣ,
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom (res hK (t.s j₀)).val =
        c * algebraMap V (FractionRing V) (eV : V) := by sorry
