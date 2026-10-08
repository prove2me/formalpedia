-- Prove2me | Theorems.Thm_ProgHedging_Convex_theorem_4_6
-- name    : ProgHedging.Convex.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:32.220474+00:00
-- url     : https://prove2.me/theorems/0c97b0f3-3218-4577-92d7-eab854809666
-- title:
--   Theorem 4.6 (convex case, without the linear-quadratic clause) — min (P) = sup (D) > −∞ and argmax (D) = −∂Φ(0)
-- statement:
--   Assume the convex case. Then
--
--   $$
--   -\infty<\min(P)=\sup(D)\ (\le\infty),
--   $$
--
--   and the set of optimal solutions of (D) is
--
--   $$
--   \operatorname{argmax}(D)=\{W^*\in\mathcal M\mid \Phi(U)\ge\Phi(0)-\langle U,W^*\rangle\ \text{for all } U\in\mathcal M\}.
--   $$
--
--   The elements of this set are exactly the $W^*$ associated with some optimal solution $X^*$ of (P) by the optimality conditions (4.1), (4.4): $W^*$ solves (D) iff there is an optimal $X^*$ of (P) with $X^*(s)\in C_s$ and $-W^*(s)\in\partial f_s(X^*(s))+N_{C_s}(X^*(s))$ for all $s$. In particular, (D) has an optimal solution whenever (P) has an optimal solution $X^*$ at which the constraint qualification holds: the only $W\in\mathcal M$ with $-W(s)\in N_{C_s}(X^*(s))$ for all $s$ is $W=0$.
--
--   This is the duality theorem that identifies the price systems produced by progressive hedging with the dual solutions.
--
--   **Formalization Note.** The last sentence of the theorem ("In the linear-quadratic case it is sure to be nonempty just from (P) being feasible") is not formalized: it needs the linear-quadratic case, which this mission does not define. The middle expression $-\partial\Phi(0)$ of (4.24) is represented by its printed second form. The printed "optimal solution $S^*$" is read $X^*$. $\Phi(0)-\langle U,W^*\rangle$ is an extended real minus a real number, so no $\infty-\infty$ arises.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 19, Theorem 4.6, (4.23)–(4.24); constraint qualification (4.2), p. 15

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Duality
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Theorem 4.6, p. 19, without the clause on the linear-quadratic case. In the convex case,
`−∞ < min (P) = sup (D)`; the optimal solutions of (D) are exactly the `W* ∈ ℳ` with
`Φ(U) ≥ Φ(0) − ⟨U, W*⟩` for all `U ∈ ℳ` (4.24); they are exactly the `W*` associated with an optimal
solution `X*` of (P) by the optimality conditions (4.1), (4.4); and the set (4.24) is nonempty if (P)
has an optimal solution `X*` at which the constraint qualification (4.2) holds. -/
theorem theorem_4_6 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (hconv : pr.ConvexCase) :
    ⊥ < pr.minP ∧ pr.minP = pr.supD ∧
    {Ws | pr.SolvesD Ws} =
      {Ws | Ws ∈ pr.M ∧ ∀ U ∈ pr.M, pr.Phi 0 - ((pr.ip U Ws : ℝ) : EReal) ≤ pr.Phi U} ∧
    (∀ Ws, pr.SolvesD Ws ↔ ∃ Xs, pr.SolvesP Xs ∧ pr.OptCond Xs Ws) ∧
    ∀ Xs, pr.SolvesP Xs →
      (∀ W ∈ pr.M, (∀ s, -W s ∈ FirstOrderOpt.ConvexTheory.normalCone (pr.C s) (Xs s)) → W = 0) →
      ∃ Ws, pr.SolvesD Ws := by sorry

end ProgHedging.Convex
