-- Prove2me | Theorems.Thm_ReluMIP_Ideal_proposition_1
-- name    : ReluMIP.Ideal.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:20.032759+00:00
-- url     : https://prove2.me/theorems/c982e7ac-8ad3-4e88-93e4-d084a824486e
-- title:
--   Proposition 1, p. 6 — (6a)–(6c) is an ideal formulation of gr(ReLU∘f; [L, U])
-- statement:
--   Let $f(x)=w\cdot x+b$ be an affine function with $w\in\mathbb R^\eta$ and $b\in\mathbb R$, over the input domain $[L,U]$ with $L_i<U_i$ for every $i$, and assume strict activity: $M^-(f)<0<M^+(f)$, where $M^+(f)=w\cdot\breve U+b$ and $M^-(f)=w\cdot\breve L+b$ are the maximum and minimum of $f$ on $[L,U]$. Then
--   $$
--   \begin{aligned}
--   &y\ge w\cdot x+b &&(6a)\\
--   &y\le\sum_{i\in I}w_i\bigl(x_i-\breve L_i(1-z)\bigr)+\Bigl(b+\sum_{i\notin I}w_i\breve U_i\Bigr)z\quad\forall I\subseteq\operatorname{supp}(w) &&(6b)\\
--   &(x,y,z)\in[L,U]\times\mathbb R_{\ge0}\times\{0,1\} &&(6c)
--   \end{aligned}
--   $$
--   is an ideal formulation of $\operatorname{gr}(\mathrm{ReLU}\circ f;[L,U])$. That is:
--
--   1. $(x,y)\in\operatorname{gr}(\mathrm{ReLU}\circ f;[L,U])$ if and only if $(x,y,z)$ satisfies (6a)–(6c) for some $z\in\{0,1\}$;
--   2. every extreme point of the LP relaxation of (6) (with $z\in[0,1]$ in place of $z\in\{0,1\}$) has $z\in\{0,1\}$.
--
--   The formulation uses only the original variables $(x,y)$ and one binary variable, with exponentially many inequalities (6b); it is the strongest possible tightening of the big-M formulation (3).
--
--   **Formalization Note** The two hypotheses $L_i<U_i$ and strict activity are the standing assumptions of §1.3 of the paper. "Ideal" follows the paper's definition (p. 3): the extreme points of the LP relaxation are integral; only $z$ is an integer variable, so integrality concerns $z$ alone.
-- source:
--   arXiv:1811.08359v2, Proposition 1, p. 6 (proof App. A.1, pp. 14–15); standing assumptions §1.3, p. 4; definition of ideal §1.1, p. 3

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting

namespace ReluMIP.Ideal

/-- Proposition 1, p. 6 (arXiv:1811.08359v2; proof App. A.1, pp. 14–15): for `f(x) = w · x + b`
over `[L, U]` (with the standing assumptions of §1.3: `Lᵢ < Uᵢ` and strict activity), (6a)–(6c) is
an ideal formulation of `gr(ReLU ∘ f; [L, U])`: together with `z ∈ {0, 1}` its LP relaxation
formulates the graph, and every extreme point of the LP relaxation has `z ∈ {0, 1}`. -/
theorem proposition_1 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) (hSA : StrictActivity w b L U) :
    IsFormulationFor (relax6 w b L U) (reluGraph w b L U) ∧ IsIdeal (relax6 w b L U) := by sorry

end ReluMIP.Ideal
