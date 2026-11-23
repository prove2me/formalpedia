-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_Supplement_lemma_3_1_c
-- name    : RobustInventory.SingleStation.Supplement.lemma_3_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:27:42.744652+00:00
-- url     : https://prove2.me/theorems/e8c8686c-de12-4e74-b063-8a4d2b6da98f
-- title:
--   Lemma 3.1(c), p. 154: nominal problem with fixed cost, thresholds (15)–(16) at the optimal ordering times
-- statement:
--   **Lemma 3.1(c).** Consider the single-station model with horizon $T$, initial stock $x_0$, fixed cost $K>0$ and unit costs $c>0$, $h\ge0$, $p>c$, and let $w$ be a demand sequence with $w_k\ge0$ for $k<T$. The nominal problem minimizes $\sum_{k<T}[K\mathbf 1_{\{u_k>0\}}+cu_k+\max(hx_{k+1},-px_{k+1})]$ over $u\ge0$, where $x_{k+1}=x_k+u_k-w_k$.
--
--   Let $t_1<\dots<t_J$ be the ordering times of any optimal solution, $t_{J+1}=T$, $L_j=t_{j+1}-t_j$ and $I_j=\lfloor(pL_j-c\mathbf 1_{\{j=J\}})/(h+p)\rfloor$. Define
--   $$S_j=\sum_{i=0}^{I_j}w_{t_j+i},\qquad s_1=x_0-\sum_{i=0}^{t_1-1}w_i,\qquad s_j=-\sum_{i=I_{j-1}+1}^{L_{j-1}-1}w_{t_{j-1}+i}\quad(j\ge2).$$
--   Then some optimal solution $v$ orders exactly at $t_1,\dots,t_J$ and, for every $j$,
--   $$x_{t_j}=s_j,\qquad x_{t_j}+v_{t_j}=S_j,$$
--   where $x$ is the stock under $v$.
--
--   Given the ordering times, this determines an optimal policy in closed form. It is the nominal result invoked in the proof of Theorem 3.2(c).
--
--   **Formalization Note** Optimal solutions with given ordering times need not be unique when the ratio in the floor is an integer: for $T=2$, $x_0=0$, $c=1$, $h=1$, $p=2$, $K=6$, $w=(5,5)$ both $(5,0)$ and $(10,0)$ are optimal, and (15) selects $10$. The stock before an order equals $s_j$, so the order is placed at $x\le s_j$, with equality included.
--
--   Differences from the source:
--   - generalization: the nominal demand w̄ → an arbitrary demand sequence w with w_k ≥ 0 on the horizon; reason: w = w̄ ≥ 0 is the printed case (demand is nonnegative, p. 156), and the proof of Theorem 3.2(c) applies the lemma to w′
--   - reading: "we have" (15) and (16) for the thresholds at the optimal ordering times → some optimal solution with exactly those ordering times has stock s_j before and S_j after each order; reason: minimizers are not unique when (pL_j − c·1{j=J})/(h+p) is an integer, so this cannot hold of every optimum; the proof exhibits one minimizer (17)–(18)
--   - reading: s_j is the reorder threshold, and Definition 3.1 orders when x < s → the stock before the order at t_j equals s_j; reason: the proof defines s_j as the stock x_{t_j}; with the strict inequality nothing would be ordered at t_j
--   - encoding: j = 1, …, J with t_{J+1} = T; sums up to t_1 − 1 and L_{j−1} − 1 → a function t on 1, …, J + 1, sums over half-open ranges, natural-number floor; reason: the same values: empty sums are zero and the numerator of I_j is positive on ordering times
--   - encoding: binary variables v_k with 0 ≤ u_k ≤ M v_k, M a large number → the fixed-cost indicator K·1{u_k > 0} of (21); reason: the two agree for M large enough; this is the convention of the published definitions
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), pp. 154–155 (PDF 5–6), Lemma 3.1(c), Eqs. (15)–(16), and its proof

import Definitions.Def_RobustInventory_SingleStation_Supplement_Thresholds

namespace RobustInventory.SingleStation.Supplement

/-- Lemma 3.1(c), p. 154, for a nonnegative demand sequence `w` and `K > 0`: if `t_1 < … < t_J`
are the ordering times of an optimal solution of the nominal problem, then some optimal solution
orders exactly at these times, and at each `t_j` its stock is `s_j` of (16) before the order and
`S_j` of (15) after it. -/
theorem lemma_3_1_c (M : Model) (hK : 0 < M.K) (w : ℕ → ℝ) (hw : ∀ k < M.T, 0 ≤ w k)
    (u : ℕ → ℝ) (hu : M.IsNominalOptimal w u)
    (J : ℕ) (t : ℕ → ℕ) (ht : IsOrderingTimes M.T u J t) :
    ∃ v : ℕ → ℝ, M.IsNominalOptimal w v ∧ IsOrderingTimes M.T v J t ∧
      ∀ j ∈ Finset.Icc 1 J,
        stockBefore M w v (t j) = lowerThreshold M w J t j ∧
        stockBefore M w v (t j) + v (t j) = upperThreshold M w J t j := by sorry

end RobustInventory.SingleStation.Supplement
