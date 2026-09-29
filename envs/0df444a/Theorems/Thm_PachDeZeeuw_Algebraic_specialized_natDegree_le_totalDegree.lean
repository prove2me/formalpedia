-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_specialized_natDegree_le_totalDegree
-- name    : PachDeZeeuw.Algebraic.specialized_natDegree_le_totalDegree
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:37.765569+00:00
-- url     : https://prove2.me/theorems/47d01b84-52f2-4e06-b592-fe07370176fb
-- title:
--   Specialized fiber degree bounded by total degree
-- statement:
--   Let $p$ be a bivariate real polynomial and $x : \mathbb{R}$ any coefficient coordinate, and write $\mathrm{Specialized0}\,x\,p$ for the univariate real polynomial obtained by evaluating the $\mathrm{XCoeff}$-coefficients of $\mathrm{Curry0}\,p$ at $x$. Then specialization cannot raise the degree:
--
--   $${(\mathrm{Specialized0}\,x\,p).\mathrm{natDegree} \leq p.\mathrm{totalDegree}.}$$
--
--   This uniform fiber-degree bound says every vertical fiber polynomial has degree at most the total degree of $p$, so each fiber contributes at most $\deg p$ common zeros. It is applied at every fiber in the pair-intersection estimates to bound the fiber size independently of $x$.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L530-L541

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.specialized_natDegree_le_totalDegree (p : MvPolynomial (Fin 2) ℝ) (x : ℝ) :
    (Specialized0 x p).natDegree ≤ p.totalDegree := by sorry
