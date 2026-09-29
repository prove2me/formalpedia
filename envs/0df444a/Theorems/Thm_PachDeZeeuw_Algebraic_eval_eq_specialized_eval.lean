-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_eval_eq_specialized_eval
-- name    : PachDeZeeuw.Algebraic.eval_eq_specialized_eval
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:32.194571+00:00
-- url     : https://prove2.me/theorems/1dea37db-fc32-4159-98ff-04b7170fec64
-- title:
--   Bivariate evaluation as specialized univariate evaluation
-- statement:
--   Let $p$ be a bivariate real polynomial and $z$ a point of the plane ($\mathrm{Point2}$). Then evaluating $p$ at $z$ equals evaluating the specialized univariate polynomial at the eliminated coordinate:
--
--   $$p(z) = \mathrm{eval}(\mathrm{elimCoord}(z),\, \mathrm{Specialized}_0(\mathrm{coeffCoord}(z), p)).$$
--
--   In coordinates $z = (y, x)$, this says $p(y,x)$ is obtained by first specializing the coefficient variable to $x$ and then evaluating at $y$. This fiber-decomposition identity is the workhorse connecting plane zero sets to univariate fibers, used in every fiber-counting argument.
-- source:
--   Lean bridge lemma (definitional unfolding or coordinate bookkeeping) for the formalization of Pach–de Zeeuw, arXiv:1308.0177, Theorem 2.1; not a literature statement; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L283-L301

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.eval_eq_specialized_eval (p : MvPolynomial (Fin 2) ℝ) (z : Point2) :
    MvPolynomial.eval (fun i => z i) p =
      Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) p) := by sorry
