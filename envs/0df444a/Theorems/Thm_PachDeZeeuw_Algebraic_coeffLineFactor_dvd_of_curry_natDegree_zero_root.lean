-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_coeffLineFactor_dvd_of_curry_natDegree_zero_root
-- name    : PachDeZeeuw.Algebraic.coeffLineFactor_dvd_of_curry_natDegree_zero_root
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:08.647708+00:00
-- url     : https://prove2.me/theorems/528bec97-12ee-4a07-b1ef-d64e71d17575
-- title:
--   Vertical-line factor from a degree-zero currying with a coefficient root
-- statement:
--   Let $h$ be a bivariate real polynomial whose currying $\mathrm{Curry}_0(h)$ (viewed as a univariate polynomial over the coefficient ring) has $\mathrm{natDegree} = 0$, and let $x \in \mathbb{R}$ be a real root of its constant coefficient, i.e. $\mathrm{eval}(x, (\mathrm{Curry}_0(h)).\mathrm{coeff}\,0) = 0$. Then the vertical-line polynomial $X_1 - x$ divides $h$:
--
--   $$\mathrm{CoeffLineFactor}(x) \mid h.$$
--
--   This extracts a vertical-line factor from a degenerate (constant-in-the-eliminated-variable) currying, and is used to classify the fibers over which specialization vanishes identically.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1209-L1219

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.coeffLineFactor_dvd_of_curry_natDegree_zero_root (h : MvPolynomial (Fin 2) ℝ)
    (hdeg0 : (Curry0 h).natDegree = 0)
    {x : ℝ}
    (hxroot : MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry0 h).coeff 0) = 0) :
    CoeffLineFactor x ∣ h := by sorry
