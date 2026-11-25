-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_flatBC_iso
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flatBC_iso
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:40.525801+00:00
-- url     : https://prove2.me/theorems/396019f2-0830-5726-af6e-16cb0d85f492
-- title:
--   Flat BC: flat BC iso
-- statement:
--   The Flat BC construction uses the flat BC iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L593-L618
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L593-L618

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
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
open TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
include H

theorem ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flatBC_iso [Module.Flat R S] [CompactSpace X]
    (hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W))
    (L : LB X) (hL : L.IsLB) (θ : LB.Sec L)
    (hθ : ∀ σ : LB.Sec L, ∃! a : R, ∀ i, σ.f i = algX p (L.U i) a * θ.f i)
    (L' : LB X') (hL' : L'.IsLB) (w : LB.Iso L' (L.pull φ)) (hw : w.IsGen) (σ' : LB.Sec L') (θ2 : LB.Sec (L.pull φ))
    (hσ : IsoRel w σ' θ2)
    (hθ2 : ∀ j (h : (L.pull φ).U j ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)), θ2.f j = (φ.appLE _ _ h).hom (θ.f (j PUnit.unit))) :
    ∀ s' : LB.Sec L', ∃! a : S, ∀ i, s'.f i = algX p' (L'.U i) a * σ'.f i := by sorry
