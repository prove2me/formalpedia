-- Prove2me | Theorems.Thm_ShipConsol_OneWH_theorem_1
-- name    : ShipConsol.OneWH.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:24.81596+00:00
-- url     : https://prove2.me/theorems/e7c1e3b7-63bf-44dc-a378-5f8c6878ba4e
-- title:
--   Theorem 1, p. 13 — for every period t an integer threshold τ_t: hold all pending orders if z > τ_t, ship all if z ≤ τ_t
-- statement:
--   Consider a retailer shipping orders from one warehouse, with a fixed shipping cost $F(p)$ for delivery in $p$ periods that is convex and non-increasing on $[1,\infty)$, a probability $\alpha \in [0,1]$ that new orders arrive in a period, and a delivery deadline of $d \ge 1$ periods. Let $V_t(z)$ be the optimal cost-to-go of the dynamic program (2)–(3), with $t$ periods to go and smallest slack time $z$ among the pending orders.
--
--   **Theorem.** For every $t \ge 1$ there is an integer threshold $\tau_t \ge 0$ such that, for every slack $1 \le z \le d$:
--   1. if $z \le \tau_t$, shipping all pending orders is optimal: $V_t(z) = F(z) + V_t(\infty)$;
--   2. if $z > \tau_t$, holding all pending orders is feasible and optimal: $t \ge 2$, $z \ge 2$ and $V_t(z) = V_{t-1}(z-1)$.
--
--   The threshold depends on the period $t$. In the last period ($t = 1$) shipping is forced and the threshold is $d$. The optimal consolidation policy is thus described by one number per period: wait while the most urgent order still has more than $\tau_t$ periods of slack, and ship everything otherwise.
--
--   **Formalization Note.** The state $z$ stands for the smallest slack among pending orders; the paper's Lemma 1, which reduces the general dynamic program (1) to (2)–(3), is not formalized, and the model is the recursion (2)–(3) itself. "Optimal" means that the corresponding branch of (2) attains the minimum, so with ties both decisions are optimal; the threshold is a natural number (a negative threshold is equivalent to $0$ since $z \ge 1$). Both implications are required: shipping is always optimal at $z = 1$, so the first implication alone would be trivial.
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), Theorem 1, p. 13

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Setting

namespace ShipConsol.OneWH
theorem theorem_1 (F : ℝ → ℝ) (hFconv : ConvexOn ℝ (Set.Ici 1) F) (hFanti : AntitoneOn F (Set.Ici 1)) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d) (t : ℕ) (ht : 1 ≤ t) : ∃ τ : ℕ, ∀ z : ℕ, 1 ≤ z → z ≤ d → (z ≤ τ → ShipOptimal F α d t z) ∧ (τ < z → HoldOptimal F α d t z) := by sorry
end ShipConsol.OneWH
