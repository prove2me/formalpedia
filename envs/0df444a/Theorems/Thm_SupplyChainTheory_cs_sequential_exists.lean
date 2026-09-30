-- Prove2me | Theorems.Thm_SupplyChainTheory_cs_sequential_exists
-- name    : SupplyChainTheory.cs_sequential_exists
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:19:10.902211+00:00
-- url     : https://prove2.me/theorems/b98accc1-e8f1-44d4-bf2e-89abf4fe05a3
-- title:
--   The sequential minimization (6.26) can be carried out: a sequentially optimal base-stock vector exists
-- statement:
--   For echelon holding costs $h_j > 0$, stockout cost $p > 0$ and lead-time demands of finite
--   mean, there is a base-stock vector $S^*$ such that each $S^*_j$ minimizes $g_j(\cdot \mid S^*)$
--   over $\mathbb{R}$, $j = 1, \dots, N$.
--
--   Theorem 6.3 defines $S^*_j$ as $\arg\min g_j(y)$ and presupposes that the minimum is
--   attained. It is: each $g_j$ is convex, grows at least linearly to the right because
--   $h_j > 0$ and to the left because the stockout term $p + h'_1 > 0$ propagates through the
--   recursion, so the sequential construction never stalls. Since $g_j(\cdot \mid S)$ depends only
--   on $S_1, \dots, S_{j-1}$, the minimizers can be chosen one stage at a time.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 196, Sect. 6.2.2, Theorem 6.3, Eq. (6.26) 'S*j = argmin{gj(y)}'

import Definitions.Def_SupplyChainTheory_multiechelon

namespace SupplyChainTheory

theorem cs_sequential_exists (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hh : ∀ j, 0 < h j) (hp : 0 < p) :
    ∃ S : ℕ → ℝ, CSSequential N h p D S := by sorry

end SupplyChainTheory
