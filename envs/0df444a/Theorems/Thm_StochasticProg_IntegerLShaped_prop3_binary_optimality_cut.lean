-- Prove2me | Theorems.Thm_StochasticProg_IntegerLShaped_prop3_binary_optimality_cut
-- name    : StochasticProg.IntegerLShaped.prop3_binary_optimality_cut
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:13:14.269388+00:00
-- url     : https://prove2.me/theorems/d64d943a-b384-42f2-956f-1b7c498bdf46
-- title:
--   Chapter 7, Proposition 3 — a valid optimality cut from one binary feasible solution
-- statement:
--   Fix a subset $S$ of the first-stage index set and write $x = \mathrm{indicator}(S)$ for
--   the binary point with $x_i = 1$, $i \in S$, and $x_i = 0$, $i \notin S$; assume $x$ is
--   first-stage feasible for the SIP, and let $q_S = Q(x)$ be its true recourse value.
--   Assume Assumption 2: a finite lower bound $L$ with $L \le \min_x \{ Q(x) \mid Ax = b,\ x
--   \in X\}$.
--
--   **Chapter 7, Proposition 3.** The optimality cut
--
--   $$
--   \theta \ge (q_S - L)\Bigl(\sum_{i \in S} x_i - \sum_{i \notin S} x_i\Bigr) - (q_S - L)(|S| - 1) + L
--   $$
--
--   is valid: for every binary, first-stage-feasible $x'$, its right-hand side never
--   exceeds the true recourse value $Q(x')$. At $x' = x$ the right-hand side equals $q_S =
--   Q(x)$ exactly; for every other binary feasible $x'$, $\delta(x',S) \le |S|-1$, and the
--   right-hand side falls to at most $L$, a valid lower bound on $Q(x')$ by Assumption 2.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 291, Chapter 7, Proposition 3

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Instance

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 7, Proposition 3 (p. 291): "Let `xi = 1, i ∈ S`, `xi = 0, i ̸∈ S` be some
first-stage feasible solution. Let `qS = Q(x)` be the corresponding recourse function
value. The optimality cut `θ ≥ (qS − L)(Σ_{i∈S} xi − Σ_{i̸∈S} xi) − (qS − L)(|S| − 1) +
L` (2.1) is valid," under Assumption 2 (`hL`, p. 291): "There exists a finite lower
bound `L` satisfying `L ≤ min_x {Q(x) | Ax = b, x ∈ X}`."

Formalized as validity for every binary SIP-feasible `x'`: the cut's right-hand side
(`cutRHS`) at `x'` never exceeds the true recourse value `Q(x')`, which is exactly what
makes it a sound lower-bounding constraint to add to the master problem. -/
theorem prop3_binary_optimality_cut (d : Data n1 n2 m1 m2 K) (L : ℝ)
    (hL : ∀ x', x' ∈ K1X d → Binary x' → (L : EReal) ≤ QY d x')
    (S : Finset (Fin n1)) (hSfeas : indicator S ∈ K1X d) (qS : ℝ)
    (hqS : (qS : EReal) = QY d (indicator S))
    (x' : Fin n1 → ℝ) (hx' : x' ∈ K1X d) (hx'bin : Binary x') :
    (cutRHS L qS S x' : EReal) ≤ QY d x' := by sorry

end StochasticProg.IntegerLShaped
