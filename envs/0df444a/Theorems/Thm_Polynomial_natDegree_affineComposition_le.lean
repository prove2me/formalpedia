-- Prove2me | Theorems.Thm_Polynomial_natDegree_affineComposition_le
-- name    : Polynomial.natDegree_affineComposition_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:31:11.371691+00:00
-- url     : https://prove2.me/theorems/233cabc4-23f5-4ebb-a794-e6d9c2158ec6
-- title:
--   Polynomial: nat Degree affine Composition le
-- statement:
--   Affine precomposition cannot increase the natural degree of a polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L42-L52
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L42-L52

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
set_option autoImplicit false
open scoped Polynomial
open Polynomial

theorem Polynomial.natDegree_affineComposition_le (p : ℂ[X]) (a b : ℂ) :
    (affineComposition p a b).natDegree ≤ p.natDegree := by sorry
