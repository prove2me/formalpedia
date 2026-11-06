-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedTensor_primeFrobeniusAlgHom_tensor_eq_map
-- name    : QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.primeFrobeniusAlgHom_tensor_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:14.423468+00:00
-- url     : https://prove2.me/theorems/b5bd7dbc-a54f-4570-a61b-c493cd621af1
-- title:
--   Prime Reduced Tensor: prime Frobenius Alg Hom tensor eq map
-- statement:
--   The Prime Reduced Tensor construction uses the prime Frobenius Alg Hom tensor eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L51-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L51-L60

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
open scoped TensorProduct
noncomputable section
variable (p : ℕ) [Fact p.Prime]

theorem QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.primeFrobeniusAlgHom_tensor_eq_map
    (C D : Type*) [CommRing C] [CommRing D]
    [Algebra (ZMod p) C] [Algebra (ZMod p) D] :
    primeFrobeniusAlgHom p (C ⊗[ZMod p] D) =
      Algebra.TensorProduct.map (primeFrobeniusAlgHom p C)
        (primeFrobeniusAlgHom p D) := by sorry
