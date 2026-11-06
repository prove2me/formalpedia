-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_SeparableDerivationExtension_separableDerivationExtension_generator
-- name    : QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.separableDerivationExtension_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:15:17.285061+00:00
-- url     : https://prove2.me/theorems/620d1fc6-ef18-4bd5-a39e-1e64ffa7ece7
-- title:
--   Separable Derivation Extension: separable Derivation Extension generator
-- statement:
--   The constructed extension has the forced value at the primitive generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SeparableDerivationExtension.lean#L585-L591
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SeparableDerivationExtension.lean#L585-L591

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
local notation3 "η" => separableGenerator (k := k) (F := F)
local notation3 "μ" => separableGeneratorMinpoly (k := k) (F := F)
local notation3 "ν" => separableGeneratorValue (k := k) (F := F)

theorem QEC.Coding.AlgebraicGeometry.SeparableDerivationExtension.separableDerivationExtension_generator (D : Derivation k (RatFunc k) M) :
    separableDerivationExtension D η = ν D := by sorry
