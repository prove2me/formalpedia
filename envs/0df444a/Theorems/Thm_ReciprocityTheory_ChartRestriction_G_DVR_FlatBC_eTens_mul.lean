-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_eTens_mul
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:10:59.385839+00:00
-- url     : https://prove2.me/theorems/3d58b806-7815-5f25-8e67-5154b297d20f
-- title:
--   Flat BC: e Tens mul
-- statement:
--   The Flat BC construction uses the e Tens mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L302-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L302-L313

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_mul (U : X.Opens) (hU : IsAffineOpen U) (u : Γ(X, U))
    (x : letI := (algX p U).toAlgebra; Γ(X, U) ⊗[R] S) :
    letI := (algX p U).toAlgebra
    eTens p p' φ H U hU ((mulL p U u).rTensor S x) = (φ.appLE U _ inf_le_left).hom u * eTens p p' φ H U hU x := by sorry
