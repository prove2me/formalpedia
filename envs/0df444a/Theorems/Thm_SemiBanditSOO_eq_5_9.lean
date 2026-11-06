-- Prove2me | Theorems.Thm_SemiBanditSOO_eq_5_9
-- name    : SemiBanditSOO.eq_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:53.838704+00:00
-- url     : https://prove2.me/theorems/fe1a96ba-98f0-4d59-810d-1b38ff25ac95
-- title:
--   (5.9) — optimism: $\bar g_u(x_{\mathrm{obs}(u)})\ge g_u(x_{\mathrm{obs}(u)})$ when $D_i\in\mathcal P_i$
-- statement:
--   Let $\mathcal P_1,\dots,\mathcal P_n$ be sets of distributions on the domains with $D_i\in\mathcal P_i$ for every $i$, and let $\bar g$ be the optimistic DP (3.3)–(3.4) for these sets and $g$ the DP (2.1)–(2.2) for $D$. Then at every node $u$ and for all observations,
--   $$\bar g_u(x_{\mathrm{obs}(u)})\ge g_u(x_{\mathrm{obs}(u)}). \qquad (5.9)$$
--
--   In a good round the optimistic values dominate the true continuation values, so the optimistic value at the root is at least $\mathrm{OPT}(D)$.
--
--   **Formalization Note.** The optimistic DP is assumed measurable, as in the paper (p.10).
--
--   Differences from the source:
--   - generalization: the confidence sets 𝒞_{i,t} of a good round (D_i ∈ 𝒞_{i,t}) → any family of sets of distributions 𝒫_i with D_i ∈ 𝒫_i; reason: the argument uses only D_i ∈ 𝒫_i; the confidence sets of a good round are an instance
--   - generalization: a finite rooted decision tree → a finite rooted DAG (every node reachable from the root, a height function strictly decreasing along edges); reason: footnote 1 (p.6) states that the analysis applies to such DAGs since obs(u) is a function of the node; a tree is an instance
--   - encoding: partial observation vectors x_obs(u) → full vectors x : (i : Fin n) → dom i, with feasibility, rewards and policies required to depend only on the coordinates in obs(u); reason: Lean convention; the same problems
--   - encoding: distributions on the domain dom(i) ⊆ [0, 1] → ProbabilityMeasure on the subtype dom i with the subspace σ-algebra; reason: no measurability of dom(i) ⊆ ℝ is needed; the same distributions
--   - encoding: the paper's standing assumption that the optimistic values are measurable (p.10) → hypothesis MeasurableDP (ḡ_u and h̄_(u,v) measurable in the observations); reason: stated in the paper; it keeps every expectation in (3.4) a genuine integral
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, proof of Theorem 3.2, (5.9), p.24

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_OptimisticDP

open MeasureTheory

namespace SemiBanditSOO

/-- **(5.9): optimism.** Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic Online
Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, proof of Theorem 3.2, (5.9), p.24.

If `D_i ∈ 𝒫_i` for every coordinate `i`, the optimistic continuation values dominate the true ones:
`ḡ_u(x_obs(u)) ≥ g_u(x_obs(u))` at every node `u` and for all observations.

**Formalization Note.** The paper states this for the confidence sets `𝒫_i = 𝒞_{i,t}` of a good
round; it is stated here for every family of sets of distributions containing the `D_i`. The
optimistic values are assumed measurable (p.10, `MeasurableDP`). -/
theorem eq_5_9 {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} (Pb : Problem n dom V)
    (D : ∀ i, ProbabilityMeasure (dom i)) (P : ∀ i, Set (ProbabilityMeasure (dom i)))
    (hD : ∀ i, D i ∈ P i) (hmeas : Pb.MeasurableDP P) :
    ∀ u x, Pb.trueVal D u x ≤ Pb.optVal P u x := by sorry

end SemiBanditSOO
