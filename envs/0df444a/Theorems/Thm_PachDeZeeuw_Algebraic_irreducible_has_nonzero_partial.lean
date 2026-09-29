-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_irreducible_has_nonzero_partial
-- name    : PachDeZeeuw.Algebraic.irreducible_has_nonzero_partial
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:47.049383+00:00
-- url     : https://prove2.me/theorems/b7e86e75-ec1d-4a98-871b-d3f92d2dc801
-- title:
--   An irreducible plane polynomial has a nonzero partial derivative
-- statement:
--   Let $h$ be an irreducible plane polynomial ($\mathrm{Irreducible}\,h$ over $\mathrm{MvPolynomial}(\mathrm{Fin}\,2, \mathbb{R})$). Then at least one of its two partial derivatives is nonzero:
--
--   $$\mathrm{pderiv}_0(h) \ne 0 \lor \mathrm{pderiv}_1(h) \ne 0.$$
--
--   Over a characteristic-zero field, only constant polynomials have all partials zero, and a nonconstant irreducible cannot be constant; this supplies the nonzero-partial hypothesis required by the factor-intersection and singularity bounds.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L881-L947

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.irreducible_has_nonzero_partial (h : PlanePoly) (hh : Irreducible h) :
    MvPolynomial.pderiv (0 : Fin 2) h ≠ 0 ∨
    MvPolynomial.pderiv (1 : Fin 2) h ≠ 0 := by sorry
