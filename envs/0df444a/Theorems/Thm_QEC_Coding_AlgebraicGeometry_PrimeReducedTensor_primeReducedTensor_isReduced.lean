-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedTensor_primeReducedTensor_isReduced
-- name    : QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.primeReducedTensor_isReduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:13.28984+00:00
-- url     : https://prove2.me/theorems/13c00ca3-0b1b-4978-9381-94960796cf69
-- title:
--   Prime Reduced Tensor: prime Reduced Tensor is Reduced
-- statement:
--   The Prime Reduced Tensor construction uses the prime Reduced Tensor is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L62-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/PrimeReducedBaseChange.lean#L62-L73

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

theorem QEC.Coding.AlgebraicGeometry.PrimeReducedTensor.primeReducedTensor_isReduced
    (C D : Type*) [CommRing C] [CommRing D]
    [Algebra (ZMod p) C] [Algebra (ZMod p) D]
    [IsReduced C] [IsReduced D] : IsReduced (C ⊗[ZMod p] D) := by sorry
