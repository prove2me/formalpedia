-- Prove2me | Theorems.Thm_SupplyChainTheory_clark_scarf_sequential
-- name    : SupplyChainTheory.clark_scarf_sequential
-- status  : Disproved
-- author  : @naimengye
-- created : 2026-09-24T00:22:59.257234+00:00
-- url     : https://prove2.me/theorems/73d61815-6844-4dd0-b250-979dadfd6d39
-- title:
--   Theorem 6.3 (Clark-Scarf): the sequentially optimized echelon base-stock vector is optimal, with cost $g_N(S^*_N)$
-- statement:
--   **Theorem 6.3.** Consider an $N$-stage serial system with echelon holding costs $h_j \ge 0$,
--   stockout cost $p \ge 0$ at stage 1 and lead-time demands $D_j$ of finite mean. Let
--   $\bar g_0(x) = (p + h'_1)x^-$ and, for $j = 1, \dots, N$,
--
--   $$ \hat g_j(x) = h_j x + \bar g_{j-1}(x), \qquad g_j(y) = \mathbb{E}[\hat g_j(y - D_j)], \qquad
--      S^*_j = \arg\min_y g_j(y), \qquad \bar g_j(x) = g_j(\min\{S^*_j, x\}). $$
--
--   Then $S^* = (S^*_j)_{j=1}^N$ is the optimal echelon base-stock vector and $g_N(S^*_N)$ is the
--   corresponding optimal cost: for every echelon base-stock vector $S$, whose expected cost is
--   $g_N(S_N \mid S)$ computed by the same recursion (6.21)-(6.23) with $S_j$ in place of $S^*_j$,
--
--   $$ g_N(S^*_N \mid S^*) \;\le\; g_N(S_N \mid S). $$
--
--   Rather than optimizing all base-stock levels simultaneously, one optimizes them one stage at
--   a time from the customer upward, each step a single-variable convex minimization. Zipkin
--   calls (6.24)-(6.27) the fundamental equations of supply chain theory; the result is Clark and
--   Scarf's (1960) for finite horizons and Federgruen and Zipkin's and Chen and Zheng's for the
--   infinite-horizon form used here.
--
--   **Formalization Note** The theorem is about the recursion: the identification of
--   $g_N(S_N \mid S)$ with the steady-state expected cost of the physical system is the book's
--   derivation (6.12)-(6.20), which is not restated. $S^*$ enters as any vector for which each
--   $S^*_j$ minimizes $g_j(\cdot \mid S^*)$; such a vector exists under $h_j > 0$, $p > 0$
--   (`cs_sequential_exists`).
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 196, Sect. 6.2.2, Theorem 6.3, Eq. (6.24)-(6.27); the recursion for a given S is Eq. (6.21)-(6.23), p. 195; after Clark and Scarf (1960) and Chen and Zheng (1994)

import Definitions.Def_SupplyChainTheory_multiechelon

namespace SupplyChainTheory

theorem clark_scarf_sequential (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (Sstar : ℕ → ℝ) (hS : CSSequential N h p D Sstar) :
    ∀ S : ℕ → ℝ, csG N h p D Sstar N (Sstar N) ≤ csG N h p D S N (S N) := by sorry

end SupplyChainTheory
