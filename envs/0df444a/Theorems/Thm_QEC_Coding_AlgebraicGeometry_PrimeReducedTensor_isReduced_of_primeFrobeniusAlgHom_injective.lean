-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedTensor_isReduced_of_primeFrobeniusAlgHom_injective
-- name    : QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.isReduced_of_primeFrobeniusAlgHom_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:00.98067+00:00
-- url     : https://prove2.me/theorems/4b37983d-ace0-4aad-ad27-b08f0225fc34
-- title:
--   Prime Reduced Tensor: is Reduced of prime Frobenius Alg Hom injective
-- statement:
--   The Prime Reduced Tensor construction uses the is Reduced of prime Frobenius Alg Hom injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L42-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L42-L49

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

theorem QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.isReduced_of_primeFrobeniusAlgHom_injective
    (C : Type*) [CommRing C] [Algebra (ZMod p) C]
    (h : Function.Injective (primeFrobeniusAlgHom p C)) : IsReduced C := by sorry
