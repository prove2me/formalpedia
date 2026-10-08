-- Prove2me | Theorems.Thm_WassDDRO_Extremal_discreteQ_mem_ball
-- name    : WassDDRO.Extremal.discreteQ_mem_ball
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:56:40.77397+00:00
-- url     : https://prove2.me/theorems/80e511ed-efc0-4ed3-ad30-189a34d79cbb
-- title:
--   Proof of Theorem 4.4, p. 17 — for every feasible point of (13), Q = (1/N)ΣΣ α_ik δ_{ξ_ik} lies in B_ε(P̂_N)
-- statement:
--   Let $N \ge 1$, let $\hat\xi_1,\dots,\hat\xi_N \in \Xi$, and let $(\alpha_{ik}, q_{ik})$ be feasible for program (13): $\frac1N\sum_{i,k}\|q_{ik}\| \le \varepsilon$, $\sum_k \alpha_{ik} = 1$, $\alpha_{ik} \ge 0$, and $\xi_{ik} := \hat\xi_i - q_{ik}/\alpha_{ik} \in \Xi$ (with $q_{ik} = 0$ when $\alpha_{ik} = 0$). Then the discrete distribution
--   $$\mathbb Q = \frac1N\sum_{i=1}^N\sum_{k=1}^K \alpha_{ik}\,\delta_{\xi_{ik}}$$
--   belongs to the Wasserstein ball $\mathbb B_\varepsilon(\widehat{\mathbb P}_N)$: it is a probability measure supported on $\Xi$ with $d_W(\mathbb Q, \widehat{\mathbb P}_N) \le \varepsilon$.
--
--   This is the first half of the second claim of Theorem 4.4: every sequence of feasible decisions of (13) yields distributions inside the ambiguity set.
--
--   **Formalization Note** The ball is the published `ambiguitySet ε 1 Ξ` around the published `empiricalDistribution`. When $\alpha_{ik} = 0$ the Lean atom is $\hat\xi_i$ and carries weight $0$.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.4 (second claim), p. 17

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting

namespace WassDDRO.Extremal

/-- Proof of Theorem 4.4, second claim, p. 17: for any feasible point (α, q) of (13), the
discrete distribution Q = (1/N) Σᵢ Σ_k α_ik δ_{ξ̂ᵢ − q_ik/α_ik} lies in the Wasserstein ball
B_ε(P̂_N); the coupling (1/N) Σᵢ Σ_k α_ik δ_{(ξ_ik, ξ̂ᵢ)} has transport cost (1/N) Σᵢ Σ_k ‖q_ik‖ ≤ ε. -/
theorem discreteQ_mem_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) (h : Feasible13 ε Ξ ξhat α q) :
    discreteQ ξhat α q ∈ WassersteinDRO.Duality.ambiguitySet ε 1 Ξ
      (WassersteinDRO.Duality.empiricalDistribution ξhat) := by sorry

end WassDDRO.Extremal
