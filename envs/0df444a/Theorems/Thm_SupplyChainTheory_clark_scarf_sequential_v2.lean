-- Prove2me | Theorems.Thm_SupplyChainTheory_clark_scarf_sequential_v2
-- name    : SupplyChainTheory.clark_scarf_sequential_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:49.798012+00:00
-- url     : https://prove2.me/theorems/e13ff24f-90b4-47f7-af6b-36a5e7f1855f
-- title:
--   Theorem 6.3 (Clark–Scarf): for $N\ge1$ stages the sequentially optimized echelon base-stock vector is optimal, with cost $g_N(S^*_N)$
-- statement:
--   **Theorem 6.3 (Clark–Scarf).** Consider an $N$-stage serial system, $N\ge1$, with echelon holding costs $h_j\ge0$, stockout cost $p\ge0$ at stage 1 and lead-time demands $D_j$ of finite mean. Let $\bar g_0(x)=(p+h'_1)x^-$ and, for $j=1,\dots,N$,
--   $$\hat g_j(x)=h_jx+\bar g_{j-1}(x),\qquad g_j(y)=\mathbb E[\hat g_j(y-D_j)],\qquad S^*_j=\arg\min_y g_j(y),\qquad \bar g_j(x)=g_j(\min\{S^*_j,x\}).$$
--   Then $S^*=(S^*_j)_{j=1}^N$ is the optimal echelon base-stock vector and $g_N(S^*_N)$ is the corresponding optimal cost: for every echelon base-stock vector $S$, whose expected cost is $g_N(S_N\mid S)$ computed by the same recursion (6.21)–(6.23) with $S_j$ in place of $S^*_j$,
--   $$g_N(S^*_N\mid S^*)\le g_N(S_N\mid S).$$
--
--   Rather than optimizing all base-stock levels simultaneously, one optimizes them one stage at a time from the customer upward, each step a single-variable convex minimization. Zipkin calls (6.24)–(6.27) the fundamental equations of supply chain theory; the result is Clark and Scarf's (1960) for finite horizons and Federgruen and Zipkin's and Chen and Zheng's for the infinite-horizon form used here.
--
--   **Formalization Note.** The retired version quantified over every $N$ including $N=0$, where `CSSequential` ranges over the empty index set and is vacuous while the conclusion compares the stage-$0$ cost (whose $\bar g_{0-1}$ reads $\bar g_0$ through natural-number subtraction) at two unrelated points (accepted disproof). The new statement adds $1\le N$ — a serial system has at least one stage — and is otherwise unchanged; with $N\ge1$ the index $j-1$ in $\hat g_j$ is only ever evaluated at $j\ge1$. The theorem is about the recursion: the identification of $g_N(S_N\mid S)$ with the steady-state expected cost of the physical system is the book's derivation (6.12)–(6.20), which is not restated. $S^*$ enters as any vector for which each $S^*_j$ minimizes $g_j(\cdot\mid S^*)$; such a vector exists under $h_j>0$, $p>0$ (`cs_sequential_exists`). Demands are arbitrary integrable real laws here, as in the retired version; the result does not need nonnegativity.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 196, Sect. 6.2.2, Theorem 6.3, Eq. (6.24)–(6.27); the recursion for a given S is Eq. (6.21)–(6.23), p. 195 (an N-stage serial system, N ≥ 1); after Clark and Scarf (1960) and Chen and Zheng (1994)

import Definitions.Def_SupplyChainTheory_multiechelon

namespace SupplyChainTheory

/-- Snyder & Shen, *Fundamentals of Supply Chain Theory*, 2nd ed., p. 196, Theorem 6.3
(Clark–Scarf): for an `N`-stage serial system (`N ≥ 1`), the echelon base-stock vector `S*`
obtained by the sequential minimization (6.24)–(6.27) is optimal: its cost `g_N(S*_N | S*)` is at
most the cost `g_N(S_N | S)` of every echelon base-stock vector `S`.

Corrected version: the serial system has at least one stage, `1 ≤ N`; the retired statement
admitted `N = 0`, where `CSSequential` is vacuous and the conclusion compares the stage-`0`
cost (which reads `ḡ_{0-1} = ḡ_0` through natural-number subtraction) at two unrelated points. -/
theorem clark_scarf_sequential_v2 (N : ℕ) (hN : 1 ≤ N) (h : ℕ → ℝ) (p : ℝ)
    (D : ℕ → MeasureTheory.Measure ℝ) [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (Sstar : ℕ → ℝ) (hS : CSSequential N h p D Sstar) :
    ∀ S : ℕ → ℝ, csG N h p D Sstar N (Sstar N) ≤ csG N h p D S N (S N) := by sorry

end SupplyChainTheory
