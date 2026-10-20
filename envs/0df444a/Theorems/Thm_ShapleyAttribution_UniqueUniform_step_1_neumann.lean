-- Prove2me | Theorems.Thm_ShapleyAttribution_UniqueUniform_step_1_neumann
-- name    : ShapleyAttribution.UniqueUniform.step_1_neumann
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:37.177748+00:00
-- url     : https://prove2.me/theorems/b4285d0d-c761-4558-815d-a70f72e42e4e
-- title:
--   Proof of Proposition 1, Step 1, p. 21 — Neumann expansion of coalition value
-- statement:
--   For a valid absorbing Markov attribution model $\mathcal M$ and coalition $X$, write $P^X$ for its transient matrix, $p_c^X$ for its one-step conversion vector, and $v(X)$ for its conversion value. Then the Neumann series converges with sum
--
--   $$v(X)=\sum_{k=0}^{\infty}\lambda^\top(P^X)^k p_c^X.$$
--
--   This is the matrix-series form of the value used in the path expansion. **Formalization Note** Absorption is stated for the original chain; validity makes every coalition matrix substochastic and dominated by it.
-- source:
--   Singal, Besbes, Desir, Goyal & Iyengar, Shapley Meets Uniform: An Axiomatic Framework for Attribution in Online Advertising, SSRN 3392721 (version of August 21, 2021), p. 21, proof of Proposition 1, Step 1

import Mathlib
import Definitions.Def_ShapleyAttribution_UniqueUniform_Model

namespace ShapleyAttribution.UniqueUniform
open Matrix

theorem step_1_neumann {m n : ℕ} (M : Model m n)
    (hM : M.Valid) (hA : M.Absorbing) (X : Finset (Fin m × Fin n)) :
    HasSum (fun k : ℕ => M.chain.lam ⬝ᵥ ((M.coalP X ∅ ^ k) *ᵥ M.coalPc X ∅))
      (M.val X ∅) := by sorry

end ShapleyAttribution.UniqueUniform
