-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_eTens_rs
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_rs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:15.156612+00:00
-- url     : https://prove2.me/theorems/d9e1c176-e9f3-52cb-8aa1-8dbc72cda82b
-- title:
--   Flat BC: e Tens rs
-- statement:
--   The Flat BC construction uses the e Tens rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L284-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L284-L300

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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))

theorem ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_rs (U U' : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U' ≤ U)
    (x : letI := (algX p U).toAlgebra; Γ(X, U) ⊗[R] S) :
    letI := (algX p U).toAlgebra; letI := (algX p U').toAlgebra
    eTens p p' φ H U' hU' ((rsL p U U' h).rTensor S x) =
      ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_inf (Scheme.Hom.preimage_mono φ h) le_rfl) (eTens p p' φ H U hU x) := by sorry
