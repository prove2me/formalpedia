-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated
-- name    : PachDeZeeuw.Algebraic.not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:57.369467+00:00
-- url     : https://prove2.me/theorems/2a3b5a63-82f2-4617-9a30-b356e43f76c1
-- title:
--   Line factor at a root of a vertical curve does not divide a non-associated $k$
-- statement:
--   Let $h$ and $k$ be irreducible bivariate real polynomials ($h_h$, $h_k$) that are not associated ($h_{not} : \neg\,\mathrm{Associated}\,h\,k$). Suppose $h$ is vertical in the sense $h_{deg0} : (\mathrm{Curry0}\,h).\mathrm{natDegree} = 0$, and let $x : \mathbb{R}$ be a root of its constant curry coefficient, i.e. $h_{xroot} : \mathrm{eval}\,(\_ \mapsto x)\,((\mathrm{Curry0}\,h).\mathrm{coeff}\,0) = 0$. Then the vertical line factor at $x$ does not divide $k$:
--
--   $${\neg\,\mathrm{CoeffLineFactor}\,x \mid k.}$$
--
--   This separates the vertical component $h$ from the non-associated curve $k$: even at a root $x$ of $h$'s coefficient, the line $X_1 = x$ is not a component of $k$. It is needed in the mixed vertical/nonvertical intersection case to ensure $k$'s specialization at $x$ is nonzero, so the fiber over $x$ can be bounded by univariate root counting.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1221-L1238

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.not_coeffLineFactor_dvd_of_root_left_zero_curry_nonassociated (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hnot : ¬ Associated h k)
    (hdeg0 : (Curry0 h).natDegree = 0)
    {x : ℝ}
    (hxroot : MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0) :
    ¬ CoeffLineFactor x ∣ k := by sorry
