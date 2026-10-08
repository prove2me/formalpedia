-- Prove2me | Theorems.Thm_ProgHedging_Nonconvex_limit_mem_M_N
-- name    : ProgHedging.Nonconvex.limit_mem_M_N
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:18.409976+00:00
-- url     : https://prove2.me/theorems/30463c3c-cc11-4dce-b4a8-2f3f770adffd
-- title:
--   Proof of Theorem 6.1 — the limits satisfy W* ∈ ℳ and X* ∈ 𝒩, and KX^ν → 0
-- statement:
--   Let $r>0$, $\delta>0$, and let $(X^\nu)$, $(W^\nu)$ be a run of progressive hedging with $\delta$-locally optimal subproblem solutions. If $X^\nu\to X^*$ and $W^\nu\to W^*$, then
--   $$W^*\in\mathcal M,\qquad KX^\nu\to0,\qquad X^*\in\mathcal N .$$
--
--   So the limit price system is a valid multiplier vector for the nonanticipativity constraint and the limit policy is implementable, although no iterate $X^\nu$ need be.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 31, proof of Theorem 6.1, paragraph after (P*)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Nonconvex_Algorithm
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone

open Filter Topology

namespace ProgHedging.Nonconvex

/-- Proof of Theorem 6.1, p. 31: if `X^ν → X*` and `W^ν → W*`, then `W* ∈ ℳ`, `K X^ν → 0`, and
`X* ∈ 𝒩`. -/
theorem limit_mem_M_N {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (X W : ℕ → ProgHedging.Convex.Policy S n) (hseq : pr.IsLocalPHSeq r δ X W)
    (Xs Ws : ProgHedging.Convex.Policy S n) (hX : Tendsto X atTop (𝓝 Xs)) (hW : Tendsto W atTop (𝓝 Ws)) :
    Ws ∈ pr.M ∧ Tendsto (fun ν => pr.K (X ν)) atTop (𝓝 0) ∧ Xs ∈ pr.N := by sorry

end ProgHedging.Nonconvex
