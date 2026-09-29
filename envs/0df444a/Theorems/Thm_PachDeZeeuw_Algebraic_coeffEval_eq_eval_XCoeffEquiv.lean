-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_coeffEval_eq_eval_XCoeffEquiv
-- name    : PachDeZeeuw.Algebraic.coeffEval_eq_eval_XCoeffEquiv
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:04.483273+00:00
-- url     : https://prove2.me/theorems/b828cadd-0480-453b-8b72-6e38539cf8e6
-- title:
--   Coefficient evaluation agrees with univariate evaluation under $\mathrm{XCoeffEquiv}$
-- statement:
--   Let $x \in \mathbb{R}$ be a real number and $r$ an element of the coefficient ring $\mathrm{XCoeff} = \mathrm{MvPolynomial}(\mathrm{Fin}\,1, \mathbb{R})$. Then evaluating the transported univariate polynomial at $x$ agrees with the coefficient evaluation homomorphism:
--
--   $$\mathrm{eval}(x, \mathrm{XCoeffEquiv}(r)) = \mathrm{coeffEval}(x, r).$$
--
--   Here `XCoeffEquiv` is the ring isomorphism between $\mathrm{XCoeff}$ and $\mathrm{Polynomial}(\mathbb{R})$. This bridge lemma lets proofs move freely between the multivariate-coefficient view (needed for currying/specialization) and the ordinary univariate-polynomial view (needed for root and degree bounds).
-- source:
--   Lean bridge lemma (definitional unfolding or coordinate bookkeeping) for the formalization of Pach–de Zeeuw, arXiv:1308.0177, Theorem 2.1; not a literature statement; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L241-L257

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.coeffEval_eq_eval_XCoeffEquiv (x : ℝ) (r : XCoeff) :
    Polynomial.eval x (XCoeffEquiv r) = coeffEval x r := by sorry
