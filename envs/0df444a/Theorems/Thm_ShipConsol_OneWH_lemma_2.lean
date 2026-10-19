-- Prove2me | Theorems.Thm_ShipConsol_OneWH_lemma_2
-- name    : ShipConsol.OneWH.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:19.087489+00:00
-- url     : https://prove2.me/theorems/2b476388-e9ca-4ed3-b384-20061e54499e
-- title:
--   Lemma 2, p. 13 — V_t(z − 1) − V_t(z) ≥ F(z − 1) − F(z) for all t ≥ 1 and z ≥ 2
-- statement:
--   Consider the one-warehouse fixed-cost model: a fixed shipping cost $F$ that is convex and non-increasing on $[1,\infty)$, an arrival probability $\alpha \in [0,1]$, a deadline $d \ge 1$, and the cost-to-go functions $V_t(z)$, $V_t(\infty)$ of the dynamic program (2)–(3) ($t$ periods to go, $z$ the smallest slack among pending orders). For all $t \ge 1$ and $2 \le z \le d$,
--   $$V_t(z-1) - V_t(z) \ \ge\ F(z-1) - F(z).$$
--
--   When the most urgent pending order loses one period of slack, the optimal cost-to-go increases by at least as much as the current shipping cost does. This comparison is what drives the threshold structure of the optimal policy (Theorem 1).
--
--   **Formalization Note.** The bound $z \le d$ is the domain $1 \le z \le d$ of the recursion (2) (the paper's state space), not an extra assumption. The paper writes out the proof only for $t \ge d$ and says the case $t < d$ is similar; the statement here, like the paper's, covers every $t \ge 1$.
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), Lemma 2, p. 13 (proof: Online Appendix, pp. OA1–OA2)

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Setting

namespace ShipConsol.OneWH
theorem lemma_2 (F : ℝ → ℝ) (hFconv : ConvexOn ℝ (Set.Ici 1) F) (hFanti : AntitoneOn F (Set.Ici 1)) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d) (t z : ℕ) (ht : 1 ≤ t) (hz : 2 ≤ z) (hzd : z ≤ d) : V F α d t (z - 1) - V F α d t z ≥ F ((z - 1 : ℕ) : ℝ) - F (z : ℝ) := by sorry
end ShipConsol.OneWH
