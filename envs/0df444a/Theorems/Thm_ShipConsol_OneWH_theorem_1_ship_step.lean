-- Prove2me | Theorems.Thm_ShipConsol_OneWH_theorem_1_ship_step
-- name    : ShipConsol.OneWH.theorem_1_ship_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:24.997323+00:00
-- url     : https://prove2.me/theorems/c95ff0fa-a8cf-4bf8-b94c-b982b826dc4c
-- title:
--   Proof of Theorem 1, p. 13 — if shipping is optimal at slack z ≥ 3, it is optimal at slack z − 1
-- statement:
--   Consider the one-warehouse fixed-cost model: a fixed shipping cost $F$ that is convex and non-increasing on $[1,\infty)$, an arrival probability $\alpha \in [0,1]$, a deadline $d \ge 1$, and the cost-to-go functions $V_t(z)$, $V_t(\infty)$ of the dynamic program (2)–(3). Fix a period $t \ge 2$ and a slack $3 \le z \le d$. If shipping all pending orders is optimal at slack $z$, that is,
--   $$V_t(z) = F(z) + V_t(\infty),$$
--   then shipping all pending orders is also optimal at slack $z-1$:
--   $$V_t(z-1) = F(z-1) + V_t(\infty).$$
--
--   The set of slacks at which shipping is optimal is therefore closed downward, which is the reduction the paper uses to prove Theorem 1.
--
--   **Formalization Note.** "Optimal" means that the ship branch of (2) attains the minimum (ties allowed). The case $t = 1$ is omitted because shipping is forced, hence always optimal, in the last period; the cases $z \le 2$ are the paper's "trivial" cases.
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), proof of Theorem 1, p. 13, "it is sufficient to show that if the optimal decision for slack time z ≥ 3 is to ship all orders, then …"

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Setting

namespace ShipConsol.OneWH
theorem theorem_1_ship_step (F : ℝ → ℝ) (hFconv : ConvexOn ℝ (Set.Ici 1) F) (hFanti : AntitoneOn F (Set.Ici 1)) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d) (t z : ℕ) (ht : 2 ≤ t) (hz : 3 ≤ z) (hzd : z ≤ d) (hship : ShipOptimal F α d t z) : ShipOptimal F α d t (z - 1) := by sorry
end ShipConsol.OneWH
