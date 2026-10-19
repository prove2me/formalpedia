-- Prove2me | Theorems.Thm_ShipConsol_OneWH_lemma_2_unrolled
-- name    : ShipConsol.OneWH.lemma_2_unrolled
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:19.781976+00:00
-- url     : https://prove2.me/theorems/8931ab44-1d09-41ac-9c3a-3e982ddaa5b8
-- title:
--   Proof of Lemma 2, p. OA1 — V_t(z) = min_{0≤j≤k} {F(z − j) + V_{t−j}(∞)}, k = min{t, z} − 1
-- statement:
--   Consider the one-warehouse fixed-cost model: a fixed shipping cost $F$ that is convex and non-increasing on $[1,\infty)$, an arrival probability $\alpha \in [0,1]$, a deadline $d \ge 1$, and the cost-to-go functions $V_t(z)$, $V_t(\infty)$ of the dynamic program (2)–(3) ($t$ periods to go, $z$ the smallest slack among pending orders). For every $t \ge 1$ and $1 \le z \le d$,
--   $$V_t(z) = \min\{F(z) + V_t(\infty),\ F(z-1) + V_{t-1}(\infty),\ \dots,\ F(z-k) + V_{t-k}(\infty)\}, \qquad k = \min\{t,z\} - 1.$$
--
--   The term $F(z-j) + V_{t-j}(\infty)$ is the cost of holding all pending orders for $j$ periods and shipping them in period $t-j$. So the cost-to-go with pending orders is determined by the no-pending-order values $V_s(\infty)$ alone. This is the first step of the paper's proof of Lemma 2.
--
--   **Formalization Note.** The minimum is a `Finset.inf'` over $j \in \{0,\dots,\min\{t,z\}-1\}$ (`Finset.range (min t z)`), so $t - j \ge 1$ and $z - j \ge 1$ in every term and the natural-number subtractions are exact. The bound $z \le d$ is the domain $1 \le z \le d$ of (2).
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), proof of Lemma 2 (Online Appendix), p. OA1, "the cost-to-go function Vt(z) can also be written as …"

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Setting

namespace ShipConsol.OneWH
theorem lemma_2_unrolled (F : ℝ → ℝ) (hFconv : ConvexOn ℝ (Set.Ici 1) F) (hFanti : AntitoneOn F (Set.Ici 1)) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) (hd : 1 ≤ d) (t z : ℕ) (ht : 1 ≤ t) (hz1 : 1 ≤ z) (hzd : z ≤ d) : V F α d t z = (Finset.range (min t z)).inf' (Finset.nonempty_range_iff.mpr (by omega)) (fun j => F ((z - j : ℕ) : ℝ) + Vinf F α d (t - j)) := by sorry
end ShipConsol.OneWH
