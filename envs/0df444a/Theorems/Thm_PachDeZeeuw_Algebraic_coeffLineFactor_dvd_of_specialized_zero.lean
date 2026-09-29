-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_coeffLineFactor_dvd_of_specialized_zero
-- name    : PachDeZeeuw.Algebraic.coeffLineFactor_dvd_of_specialized_zero
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:17.746516+00:00
-- url     : https://prove2.me/theorems/54371937-7b58-4cee-b0df-53163cc86547
-- title:
--   Vertical-line factor from a vanishing specialization
-- statement:
--   Let $p$ be a bivariate real polynomial and $x \in \mathbb{R}$ a real number such that the specialization of $p$ at $x$ vanishes identically, $\mathrm{Specialized}_0(x, p) = 0$. Then the vertical-line polynomial divides $p$:
--
--   $$\mathrm{CoeffLineFactor}(x) \mid p, \quad \text{i.e. } (X_1 - x) \mid p.$$
--
--   This is the key algebraic step linking a degenerate fiber (specialization identically zero) to a geometric vertical-line component, used to show that nonvertical curves have only finitely many bad fibers.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L626-L700

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.coeffLineFactor_dvd_of_specialized_zero (p : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (hx : Specialized0 x p = 0) :
    CoeffLineFactor x ∣ p := by sorry
