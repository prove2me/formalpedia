-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_mem_CoeffLineZeroSet
-- name    : PachDeZeeuw.Algebraic.mem_CoeffLineZeroSet
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:09.727461+00:00
-- url     : https://prove2.me/theorems/50e87857-5130-485a-8849-c5ca01610983
-- title:
--   Membership characterization of coefficient-line zero sets
-- statement:
--   Let $a$ be a univariate coefficient polynomial in $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,1)\,\mathbb{R}$ and $p$ a plane point ($\mathrm{Point2}$). Then membership $p \in \mathrm{CoeffLineZeroSet}\,a$ holds exactly when $a$ vanishes at the coefficient coordinate $p\,1$,
--
--   $$\mathrm{eval}\,(\_ \mapsto p\,1)\,a = 0,$$
--
--   and the two conditions coincide by definitional unfolding (`Iff.rfl`).
--
--   In geometric terms, $\mathrm{CoeffLineZeroSet}\,a$ is the set of points whose coefficient coordinate $p\,1$ is a real root of $a$, that is, a union of lines of constant coefficient coordinate, one for each real root. This `simp` lemma is used to unfold line--curve intersections into root conditions on fibers.
-- source:
--   Lean bridge lemma (definitional unfolding or coordinate bookkeeping) for the formalization of Pach–de Zeeuw, arXiv:1308.0177, Theorem 2.1; not a literature statement; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L621-L624

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

@[simp]
theorem PachDeZeeuw.Algebraic.mem_CoeffLineZeroSet {a : MvPolynomial (Fin 1) ℝ}
    {p : Point2} :
    p ∈ CoeffLineZeroSet a ↔ MvPolynomial.eval (fun _ : Fin 1 => p 1) a = 0 := by sorry
