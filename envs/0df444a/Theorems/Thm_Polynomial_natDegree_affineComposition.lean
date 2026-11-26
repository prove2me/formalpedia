-- Prove2me | Theorems.Thm_Polynomial_natDegree_affineComposition
-- name    : Polynomial.natDegree_affineComposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:31:27.221669+00:00
-- url     : https://prove2.me/theorems/1f7effed-d538-4e93-be08-049d4a61df28
-- title:
--   Polynomial: nat Degree affine Composition
-- statement:
--   Precomposition by a nonconstant affine map preserves natural degree.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L55-L61
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L55-L61

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
set_option autoImplicit false
open scoped Polynomial
open Polynomial

theorem Polynomial.natDegree_affineComposition (p : ℂ[X]) {a b : ℂ} (ha : a ≠ 0) :
    (affineComposition p a b).natDegree = p.natDegree := by sorry
