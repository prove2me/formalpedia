-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedTensor_primeFrobeniusAlgHom_injective
-- name    : QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.primeFrobeniusAlgHom_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:57.933125+00:00
-- url     : https://prove2.me/theorems/b42c2aef-2eaa-4a16-be10-ce83c67f16e1
-- title:
--   Prime Reduced Tensor: prime Frobenius Alg Hom injective
-- statement:
--   The Prime Reduced Tensor construction uses the prime Frobenius Alg Hom injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L31-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L31-L40

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

theorem QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.primeFrobeniusAlgHom_injective
    (C : Type*) [CommRing C] [Algebra (ZMod p) C] [IsReduced C] :
    Function.Injective (primeFrobeniusAlgHom p C) := by sorry
