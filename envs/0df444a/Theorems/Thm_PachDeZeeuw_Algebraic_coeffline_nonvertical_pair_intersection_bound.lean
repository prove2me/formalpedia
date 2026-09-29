-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_coeffline_nonvertical_pair_intersection_bound
-- name    : PachDeZeeuw.Algebraic.coeffline_nonvertical_pair_intersection_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:37:17.570697+00:00
-- url     : https://prove2.me/theorems/e0ad9c71-38e0-4130-b6d8-bc2e48236f41
-- title:
--   B\u00e9zout bound for a coefficient line against a nonvertical curve
-- statement:
--   Let $a$ be a nonzero univariate coefficient polynomial of total degree at most $d_1$ and $q$ a nonzero bivariate real polynomial of total degree at most $d_2$, with currying of positive $\mathrm{natDegree}$ ($0 < (\mathrm{Curry}_0(q)).\mathrm{natDegree}$), and assume no root $x$ of $a$ yields a vertical-line factor of $q$ ($\forall x, a(x) = 0 \Rightarrow \neg\,\mathrm{CoeffLineFactor}(x) \mid q$). Then the intersection of the coefficient-line zero set with the plane curve is finite with an explicit product bound:
--
--   $$|\mathrm{CoeffLineZeroSet}(a) \cap {Z}(q)| \le d_1 \cdot d_2.$$
--
--   This handles the mixed vertical/nonvertical intersection case in the B\u00e9zout development: the non-divisibility hypothesis rules out shared vertical components, after which each of the at most $d_1$ vertical lines meets the curve in at most $d_2$ points.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L914-L1067

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.coeffline_nonvertical_pair_intersection_bound {d₁ : ℕ} {d₂ : ℕ} (a : XCoeff) (q : MvPolynomial (Fin 2) ℝ)
    (ha0 : a ≠ 0) (_hq0 : q ≠ 0)
    (hadeg : a.totalDegree ≤ d₁)
    (hqdeg : q.totalDegree ≤ d₂)
    (_hq0deg : 0 < (Curry0 q).natDegree)
    (hnotDiv :
      ∀ x : ℝ,
        MvPolynomial.eval (fun _ : Fin 1 => x) a = 0 →
          ¬ CoeffLineFactor x ∣ q) :
    (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).Finite ∧
      (CoeffLineZeroSet a ∩ PlaneCurveZeroSet q).ncard ≤ d₁ * d₂ := by sorry
