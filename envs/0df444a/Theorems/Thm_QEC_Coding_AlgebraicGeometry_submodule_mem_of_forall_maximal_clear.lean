-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_submodule_mem_of_forall_maximal_clear
-- name    : QEC.Coding.AlgebraicGeometry.submodule_mem_of_forall_maximal_clear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:06:34.816733+00:00
-- url     : https://prove2.me/theorems/1c76cd5e-dd5c-4da6-9e8c-e78307c3e77d
-- title:
--   Algebraic Geometry: submodule mem of forall maximal clear
-- statement:
--   Denominators outside every maximal ideal force actual submodule membership via the ideal of clearing scalars.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerImage.lean#L23-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerImage.lean#L23-L38

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (A W : Type*) [CommRing A] [AddCommGroup W] [Module A W]

theorem QEC.Coding.AlgebraicGeometry.submodule_mem_of_forall_maximal_clear (U : Submodule A W) (omega : W)
    (h : ∀ (P : Ideal A) [P.IsMaximal], ∃ s : A, s ∉ P ∧ s • omega ∈ U) :
    omega ∈ U := by sorry
