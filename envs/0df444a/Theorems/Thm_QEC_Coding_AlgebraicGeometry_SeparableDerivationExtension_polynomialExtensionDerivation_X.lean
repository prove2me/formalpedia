-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_SeparableDerivationExtension_polynomialExtensionDerivation_X
-- name    : QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.polynomialExtensionDerivation_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:13.977834+00:00
-- url     : https://prove2.me/theorems/90480932-f2d7-4039-8c81-52cabe1261be
-- title:
--   Separable Derivation Extension: polynomial Extension Derivation X
-- statement:
--   The polynomial extension derivation has its prescribed value at `X`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SeparableDerivationExtension.lean#L385-L389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SeparableDerivationExtension.lean#L385-L389

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
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.moduleKAEval

theorem QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.polynomialExtensionDerivation_X (D : Derivation k (RatFunc k) M) (y : F) (v : M) :
    polynomialExtensionDerivation D y v Polynomial.X = Module.AEval.of (RatFunc k) M y v := by sorry
