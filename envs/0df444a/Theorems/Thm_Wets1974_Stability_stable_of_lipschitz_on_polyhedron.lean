-- Prove2me | Theorems.Thm_Wets1974_Stability_stable_of_lipschitz_on_polyhedron
-- name    : Wets1974.Stability.stable_of_lipschitz_on_polyhedron
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:36:57.062417+00:00
-- url     : https://prove2.me/theorems/42673c31-95d5-4158-ac35-9ba892e9aaac
-- title:
--   Lemma 8.9 — a finite program with convex objective Lipschitz on a polyhedron is stable
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, $P\subseteq\mathbb R^n$ a convex polyhedron (finitely many linear inequalities), and $f:\mathbb R^n\to\mathbb R$ a function that is convex on $P$ and Lipschitz on $P$. Consider the mathematical program (8.10),
--   $$\text{minimize } f(x)\quad\text{subject to } Ax=b,\ x\ge0,$$
--   where $f$ is regarded as $+\infty$ outside $P$, so that the feasible set is $P\cap\{x: Ax=b,\ x\ge0\}$. If (8.10) is finite, i.e. its optimal value $v=\inf\{f(x): x\in P,\ Ax=b,\ x\ge0\}$ is a real number, then (8.10) is **stable**: there is $\pi\in\mathbb R^m$ with
--   $$v\le f(x)+\pi\,(b-Ax)\qquad\text{for every }x\in P\text{ with }x\ge0 .$$
--
--   This is the purely convex-analytic step behind Theorem 8.11 (the paper cites it to Walkup and Wets, 1969): a Lipschitz convex objective on a polyhedral domain rules out the infinite-slope behaviour of the perturbation function that destroys stability.
--
--   **Formalization Note** "Convex and Lipschitz on a polyhedron" is read as: the objective's domain is the polyhedron $P$ (the objective is $+\infty$ off $P$), and on $P$ it is finite, convex and Lipschitz. This is how the lemma is applied to $Z$, whose domain is $K_2$; a function finite and convex on all of $\mathbb R^n$ would make the Lipschitz hypothesis superfluous. Lipschitz is `LipschitzOnWith` for the sup norm, equivalent to the Euclidean one for the existence of a constant. "Stable" is the Kuhn–Tucker form of Definition 8.1(iv) given in the definition file: the dual obtained by perturbing $b$ is solvable and has no duality gap.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, p. 337, Lemma 8.9 (Eq. (8.10)); stability as in Definition 8.1(iv), p. 334

import Mathlib
import Definitions.Def_Wets1974_Stability_ConvexAnalysis

namespace Wets1974.Stability

open Matrix

/-- Lemma 8.9, p. 337: minimize `f(x)` subject to `A x = b`, `x ≥ 0` (8.10), where `f` is
convex and Lipschitz on a polyhedron `P` (its domain), and (8.10) is finite; then (8.10) is
stable. -/
theorem stable_of_lipschitz_on_polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (P : Set (Fin n → ℝ)) (hP : IsPolyhedron P) (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ P f) (hlip : ∃ L : NNReal, LipschitzOnWith L f P)
    (hfin : IsFiniteProgram (fun x => (f x : EReal)) P A b) :
    IsStable (fun x => (f x : EReal)) P A b := by sorry

end Wets1974.Stability
