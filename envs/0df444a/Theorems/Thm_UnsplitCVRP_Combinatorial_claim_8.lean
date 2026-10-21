-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_claim_8
-- name    : UnsplitCVRP.Combinatorial.claim_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:00.870837+00:00
-- url     : https://prove2.me/theorems/ab3250ba-bfa3-482e-9d47-7651ea047f78
-- title:
--   Claim 8, p. 6 — probability that a client is bad
-- statement:
--   Number the clients of a depot tour in visiting order. For $\delta\in[0,1/2]$, draw the offset $\theta$ uniformly from $[0,1-\delta]$ and place tile endpoints at $\theta+\ell(1-\delta)$ for integers $\ell\ge0$. Client $v_i$ is bad when an endpoint lies in its cumulative-demand interval. Then
--   $$
--   \Pr[v_i\text{ is bad}]=\min\left\{1,\frac{d_{v_i}}{1-\delta}\right\}.
--   $$
--   This probability controls the expected cost of added depot edges in the tank construction.
--
--   **Formalization Note** The client index is zero-based in Lean. Probability is Lebesgue volume of the event within $[0,1-\delta]$, divided by $1-\delta$.
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 6, Claim 8 (event (2) on p. 5)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace UnsplitCVRP.Combinatorial

/-- Claim 8, p. 6: probability of a client's demand interval meeting a tile endpoint. -/
theorem claim_8 {n : ℕ} (d : Fin (n + 1) → ℝ) (hd : Demands d)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (A : List (Fin (n + 1))) (hAn : A.Nodup)
    (hA : (0 : Fin (n + 1)) ∉ A)
    (i : ℕ) (hi : i < A.length) :
    (MeasureTheory.volume {θ : ℝ | θ ∈ Set.Icc 0 (1 - δ) ∧ IsBad d δ A i θ}).toReal /
        (1 - δ) =
      min 1 (d (A.getD i 0) / (1 - δ)) := by sorry

end UnsplitCVRP.Combinatorial
