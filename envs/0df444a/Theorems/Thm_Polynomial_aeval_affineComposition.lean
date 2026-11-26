-- Prove2me | Theorems.Thm_Polynomial_aeval_affineComposition
-- name    : Polynomial.aeval_affineComposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:13.042381+00:00
-- url     : https://prove2.me/theorems/c2d0e8b3-5acf-595f-b4ae-b04862edce93
-- title:
--   Polynomial: aeval affine Composition
-- statement:
--   Algebra-valued evaluation commutes with affine precomposition.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L35-L39
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L35-L39

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
set_option autoImplicit false
open scoped Polynomial
open Polynomial

theorem Polynomial.aeval_affineComposition {A : Type*} [Semiring A] [Algebra ℂ A]
    (p : ℂ[X]) (a b : ℂ) (x : A) :
    aeval x (affineComposition p a b) = aeval (a • x + b • (1 : A)) p := by sorry
