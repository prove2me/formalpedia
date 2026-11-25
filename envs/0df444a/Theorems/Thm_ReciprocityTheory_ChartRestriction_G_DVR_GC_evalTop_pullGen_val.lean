-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_pullGen_val
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_pullGen_val
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:16:43.266897+00:00
-- url     : https://prove2.me/theorems/78fac510-c482-4159-a243-62b543342ee5
-- title:
--   GC: eval Top pull Gen val
-- statement:
--   The GC construction uses the eval Top pull Gen val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L219-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L219-L228

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_pullGen_val {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom f))
    {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of A) ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (j : K → L.ι) (hU : LB.wchart L φ j = ⊤)
    (hU' : LB.wchart L (fun k => g ≫ φ k) j = ⊤) :
    evalTop _ hU' ((LB.pullGen L φ ε c g).s j).val = f (evalTop _ hU (c.s j).val) := by sorry
