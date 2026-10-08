-- Prove2me | Theorems.Thm_VanderbeiLP_Networks_integrality_theorem
-- name    : VanderbeiLP.Networks.integrality_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T18:57:08.509976+00:00
-- url     : https://prove2.me/theorems/e3b5d1f7-1da8-4b09-bf50-a3eb9a74f86b
-- title:
--   Theorem 14.2 — Integrality Theorem
-- statement:
--   Let $(N,A)$ be a connected network with supplies $b_i$, $\sum_{i\in N}b_i=0$, and suppose the data are integers: every $b_i\in\mathbb Z$. Fix a root node $r$. Then every basic feasible solution $x$ of the network flow problem (14.1) is integral:
--   $$x_{ij}\in\mathbb Z\qquad\text{for every arc }(i,j)\in A.$$
--   In particular every basic optimal solution assigns integer flow to every arc, whatever the costs $c_{ij}$.
--
--   The theorem makes network flow problems with integer data integer programs that the simplex method solves exactly; it is the tool behind König's Theorem 14.3.
--
--   **Formalization Note** "Integer data" means integral supplies and demands only (p. 215); the costs play no role and are omitted. A basic optimal solution is a basic feasible solution, so the "in particular" clause of the book is contained in the statement. The standing assumptions $\sum_i b_i=0$ (p. 200) and connectedness (p. 202) are hypotheses.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 216 (PDF 227), Theorem 14.2; integer data p. 215; standing assumptions pp. 200, 202

import Mathlib
import Definitions.Def_VanderbeiLP_Networks_Network

namespace VanderbeiLP.Networks

/-- **Theorem 14.2, Integrality Theorem** (Vanderbei, *Linear Programming*, 4th ed., p. 216).
For a network flow problem (14.1) on a connected network with integer supplies/demands
(`∑ b_i = 0`), every basic feasible solution assigns integer flow to every arc. (Every basic
optimal solution is in particular a basic feasible solution.) -/
theorem integrality_theorem {N : Type*} [Fintype N] [DecidableEq N]
    (A : Finset (N × N)) (hA : IsNetwork A) (hconn : IsConnectedNetwork A)
    (b : N → ℝ) (hsum : ∑ i, b i = 0) (hb : ∀ i, ∃ z : ℤ, b i = z)
    (r : N) (x : N × N → ℝ) (hx : IsBasicFeasibleFlow A b r x) :
    ∀ a ∈ A, ∃ z : ℤ, x a = z := by sorry

end VanderbeiLP.Networks
