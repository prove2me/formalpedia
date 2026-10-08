-- Prove2me | Theorems.Thm_ReluMIP_Ideal_multiple_choice_ideal
-- name    : ReluMIP.Ideal.multiple_choice_ideal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:10.941261+00:00
-- url     : https://prove2.me/theorems/1ced023c-43ec-4894-9374-efdc7196a1fc
-- title:
--   §2.2, (5), pp. 5–6 — the multiple choice formulation is an ideal extended formulation of the ReLU graph
-- statement:
--   Let $f(x)=w\cdot x+b$ with $w\in\mathbb R^\eta$, $b\in\mathbb R$, and let $L,U\in\mathbb R^\eta$ with $L_i<U_i$ for every $i$. Let $\widetilde R_5$ be the lifted LP relaxation of (5) in $(x,y,z,x^0,x^1,y^0,y^1)$, and $R_5$ its projection onto $(x,y,z)$: the points $(x,y,z)$ with $0\le z\le1$ for which there are $x^0,x^1,y^0,y^1$ with
--   $$
--   (x,y)=(x^0,y^0)+(x^1,y^1),\quad y^0=0\ge w\cdot x^0+b(1-z),\quad y^1=w\cdot x^1+bz\ge0,\quad L(1-z)\le x^0\le U(1-z),\quad Lz\le x^1\le Uz .
--   $$
--   Then:
--
--   1. Every extreme point of $\widetilde R_5$ has $z\in\{0,1\}$, so (5) is ideal in its lifted space;
--   2. $R_5$ with $z\in\{0,1\}$ is a formulation of $\operatorname{gr}(\mathrm{ReLU}\circ f;[L,U])$: $(x,y)$ lies on the graph if and only if $(x,y,z)\in R_5$ for some $z\in\{0,1\}$;
--   3. $R_5$ is the convex hull of its points with $z\in\{0,1\}$:
--   $$
--   R_5=\operatorname{conv}\{(x,y,z)\in R_5 : z\in\{0,1\}\}.
--   $$
--
--   The paper cites this fact from the literature on piecewise linear functions and from Balas's disjunctive programming; it is the starting point of the proof of Proposition 1.
--
--   **Formalization Note** The projected hull identity is the consequence of lifted ideality used in Appendix A.1. Strict activity is not assumed; the statement also holds without it.
-- source:
--   arXiv:1811.08359v2, §2.2, display (5a)–(5f), pp. 5–6

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting
import Definitions.Def_ReluMIP_Ideal_Lifted5

namespace ReluMIP.Ideal

/-- §2.2, display (5), pp. 5–6 (arXiv:1811.08359v2): the multiple-choice formulation (5) is an
ideal extended formulation of `gr(ReLU ∘ f; [L, U])`. Its lifted LP relaxation has binary
extreme points in `z`; with `z ∈ {0,1}` it formulates the graph; and its projection to
`(x,y,z)` is the convex hull of its points with `z ∈ {0,1}`. -/
theorem multiple_choice_ideal {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) :
    (∀ p ∈ Set.extremePoints ℝ (relax5Lift w b L U), p.1.2.2 = 0 ∨ p.1.2.2 = 1) ∧
      IsFormulationFor (relax5 w b L U) (reluGraph w b L U) ∧
      relax5 w b L U = convexHull ℝ {p | p ∈ relax5 w b L U ∧ (p.2.2 = 0 ∨ p.2.2 = 1)} := by sorry

end ReluMIP.Ideal
