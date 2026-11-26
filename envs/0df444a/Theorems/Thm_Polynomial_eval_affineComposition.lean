-- Prove2me | Theorems.Thm_Polynomial_eval_affineComposition
-- name    : Polynomial.eval_affineComposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:08.527605+00:00
-- url     : https://prove2.me/theorems/affe903c-298e-5609-9230-5eeb04089ee4
-- title:
--   Polynomial: eval affine Composition
-- statement:
--   Evaluating an affine composition is evaluation after the corresponding scalar affine map.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L29-L31
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L29-L31

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
set_option autoImplicit false
open scoped Polynomial
open Polynomial

theorem Polynomial.eval_affineComposition (p : ℂ[X]) (a b z : ℂ) :
    (affineComposition p a b).eval z = p.eval (a * z + b) := by sorry
