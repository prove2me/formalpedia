-- Prove2me | Theorems.Thm_Wets1974_Stability_stable_of_K2_polyhedral
-- name    : Wets1974.Stability.stable_of_K2_polyhedral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:38:35.011997+00:00
-- url     : https://prove2.me/theorems/3fe6bca0-84cc-43f1-9183-cf1362679cb2
-- title:
--   Theorem 8.11 — with $K_2$ polyhedral and finite value, the deterministic equivalent convex program (8.2) is stable
-- statement:
--   Consider a stochastic program with fixed recourse whose random element $\xi$, with law a probability measure $\mu$, satisfies the weak covariance condition (Definition 2.2), and whose recourse matrix $W$ has full row rank (standing assumption, p. 312). Let $Z(x)=\bar cx+\mathcal Q(x)$ be the objective (3.1) and $K_2$ the induced constraint set (Corollary 4.5). Consider the deterministic equivalent convex program (8.2),
--   $$\text{minimize } Z(x)\quad\text{subject to } Ax=b,\ x\in K_2,\ x\ge0 .$$
--   Suppose that
--
--   1. $K_2$ is a convex polyhedron, and
--   2. the program is finite: $v=\inf\{Z(x): x\in K_1\cap K_2\}$ is a real number.
--
--   Then (8.2) is **stable**: there is a multiplier $\pi\in\mathbb R^m$ for the fixed constraints $Ax=b$ with
--   $$v\le Z(x)+\pi\,(b-Ax)\qquad\text{for every }x\in K_2\text{ with }x\ge0 .$$
--   Equivalently, the dual program (8.3), $\sup\{u \mid u\le\mathcal Q(x)+(\bar c-\pi A)x+\pi b\ \ \forall x\in K_2\cap\{x\ge0\}\}$, is solvable and there is no duality gap.
--
--   Stability means that the optimal value reacts at a bounded rate to perturbations $b\mapsto b-u$ of the first-stage constraints. The paper's Example 8.5 shows that the weak covariance condition cannot be dropped.
--
--   **Formalization Note** The paper states the hypothesis as "$K$ is polyhedral" with $K=K_1\cap K_2$. Read literally, that is false: with $K_2$ the closed unit disk in $\mathbb R^2$ (produced by $T(\xi)$ uniform on the unit circle, $p\equiv1$, $W=(1)$, $q\equiv0$), $c\equiv(-1,0)$, and $K_1=\{x_2=1,\ x\ge0\}$, the set $K=\{(0,1)\}$ is polyhedral and the value $0$ is finite, but $-x_1+\pi(1-x_2)<0$ at $x=(\sqrt{2h-h^2},1-h)$ for small $h>0$, so no multiplier exists. The paper's own sentence before Lemma 8.9 ties "polyhedral region" to $K_2$ (Theorems 4.7, 4.10 concern $K_2$), and the proof applies Lemma 8.9 with the objective's domain $K_2$; the statement here uses $K_2$. In (8.3) the page writes $c$ where (3.1) and (8.2) require $\bar c$. The middle constraint of (8.2), written with the polar matrix $W^*$, is the constraint $x\in K_2$ by Corollary 4.5.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, p. 337, Theorem 8.11; program (8.2) and dual (8.3), p. 334; Definition 8.1(iv), p. 334

import Mathlib
import Definitions.Def_Wets1974_Stability_Model

namespace Wets1974.Stability

open MeasureTheory Matrix

/-- Theorem 8.11, p. 337 (with "K₂ polyhedral", see the natural-language statement): for a
stochastic program with fixed recourse satisfying the weak covariance condition, with `W` of
full row rank (p. 312), if the induced constraint set `K₂` is a polyhedron and the program is
finite, then the deterministic equivalent convex program (8.2),
`inf {Z(x) | A x = b, x ∈ K₂, x ≥ 0}`, is stable. -/
theorem stable_of_K2_polyhedral {n nb mb m : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (hcov : WeakCovariance μ)
    (W : Matrix (Fin mb) (Fin nb) ℝ) (hW : FullRowRank W)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hK2 : IsPolyhedron (K2 μ W))
    (hfin : IsFiniteProgram (Z μ W) (K2 μ W) A b) :
    IsStable (Z μ W) (K2 μ W) A b := by sorry

end Wets1974.Stability
