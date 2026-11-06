-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_SeparableDerivationExtension_polynomialExtensionValue_X
-- name    : QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.polynomialExtensionValue_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:45.903576+00:00
-- url     : https://prove2.me/theorems/5feb299f-28a2-4e08-9910-4de6606bfa40
-- title:
--   Separable Derivation Extension: polynomial Extension Value X
-- statement:
--   The Separable Derivation Extension construction uses the polynomial Extension Value X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SeparableDerivationExtension.lean#L143-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SeparableDerivationExtension.lean#L143-L148

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Polynomial.Module.AEval
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension
open scoped RatFunc
variable {k F M : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
variable [AddCommGroup M] [Module k M] [Module (RatFunc k) M] [Module F M]
variable [IsScalarTower k F M] [IsScalarTower (RatFunc k) F M] [IsScalarTower k (RatFunc k) M]

theorem QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.polynomialExtensionValue_X (D : Derivation k (RatFunc k) M) (y : F) (v : M) :
    polynomialExtensionValue D y v Polynomial.X = v := by sorry
