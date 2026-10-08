-- Prove2me | Theorems.Thm_RunwayCPS_DiscreteTime_min_cost_path_optimal
-- name    : RunwayCPS.DiscreteTime.min_cost_path_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:36.449204+00:00
-- url     : https://prove2.me/theorems/2f7af8f5-070f-4687-aee2-9cf680b90375
-- title:
--   §6.2 — minimum-cost source-sink paths of the modified network give optimal schedules without the triangle inequality
-- statement:
--   Consider a discrete-time runway instance with $n\ge 1$ aircraft, maximum shift $k\ge 1$, positive landing costs $c_a(t)>0$, and separations that need not satisfy the triangle inequality but satisfy the polygon inequalities of three or more hops. Weight each arc of the modified network of §6.2 that enters a node $(i,t,d)$ by $c_{\mathrm{fin}(i)}(t)$, and arcs to the sink by $0$. Then:
--
--   1. a feasible schedule exists if and only if the modified network has a source-sink path;
--   2. for every real $C$, $C$ is the minimum cost of a feasible schedule if and only if $C$ is the minimum cost of a source-sink path:
--   $$
--   \min_{(\sigma,t)\ \text{feasible}}\ \sum_{p} c_{\sigma(p)}(t_p)\;=\;\min_{\text{paths } P}\ \sum_{p=1}^{n} c_{\mathrm{fin}(i_p)}(t_p),
--   $$
--   with either minimum attained exactly when the other is;
--   3. every minimum-cost source-sink path represents a feasible schedule, and that schedule is optimal.
--
--   This is the closing claim of §6.2: the scheduling problem with arbitrary separable costs and separations that violate the triangle inequality is solved by a shortest-path computation.
--
--   **Formalization Note** Minima are stated with `IsLeast` on the sets of costs. The polygon-inequality hypothesis is added (Lemma 5 fails without it). $\Gamma(i)$ is the full time window. The paper's arc cost $c(i,t)$ is read as $c_{\mathrm{fin}(i)}(t)$. Positivity of costs is the paper's assumption and is not needed for the conclusion.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1660, §6.2, closing paragraph (from Lemmas 5 and 6)

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_ModifiedNetwork

namespace RunwayCPS.DiscreteTime

/-- §6.2, closing paragraph (p. 1660): with `k ≥ 1`, positive costs, and separations that need
not satisfy the triangle inequality but satisfy the polygon inequalities of three or more hops,
1. a feasible schedule exists if and only if the modified network has a source-sink path;
2. the minimum cost of a feasible schedule equals the minimum cost of a source-sink path
   (each arc entering `(i, t, d)` weighted `c_{fin(i)}(t)`, sink arcs weighted `0`);
3. every minimum-cost source-sink path represents a feasible schedule that is optimal. -/
theorem min_cost_path_optimal {n : ℕ} [NeZero n] (I : Instance n) (hk : 1 ≤ I.k)
    (hpoly : PolygonIneq I.δ) (hc : ∀ a t, 0 < I.c a t) :
    ((∃ (σ : Fin n → Fin n) (t : Fin n → ℕ), IsFeasible I σ t) ↔
        ∃ P : ℕ → MNode n, IsMPath I P) ∧
      (∀ C : ℝ, IsLeast (scheduleCosts I) C ↔ IsLeast (pathCosts I) C) ∧
      (∀ P : ℕ → MNode n, IsMPath I P → IsLeast (pathCosts I) (pathCost I P) →
        IsFeasible I (mSeq P) (mTimes P) ∧
          IsLeast (scheduleCosts I) (cost I (mSeq P) (mTimes P))) := by sorry

end RunwayCPS.DiscreteTime
