-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_18
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_18
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:22.834732+00:00
-- url     : https://prove2.me/theorems/9774deb6-d90a-4aa1-90ef-51742428c8e0
-- title:
--   Rank-cut certificate at D* — certified p-cells on [3789/4096, 3891/4096]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [3789/4096, 3891/4096]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [3789/4096, 3891/4096] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_18 :
    CellOK (3789 / 4096 : ℝ) (3891 / 4096 : ℝ) (260981543 / 22356376 : ℝ) (-5492498280 / 535834351 : ℝ) (0 : ℝ)
      ![(17945833 / 41052225 : ℝ), (152214245 / 893934488 : ℝ), (-1823359282361 / 954370475797 : ℝ), (-3834253763511 / 887146093561 : ℝ), (-3278850032969 / 520496921974 : ℝ), (-7792056513 / 979915783 : ℝ), (-5501319434 / 542703523 : ℝ), (-1438267624 / 222806879 : ℝ), (-11077755525 / 666185122 : ℝ)]
      ![(-203856103 / 442995391 : ℝ), (-53088661 / 299395630 : ℝ), (261170057 / 126454062 : ℝ), (4483149009 / 959537878 : ℝ), (2947916429 / 432888887 : ℝ), (8327726121 / 968785768 : ℝ), (5208136825 / 475272647 : ℝ), (6967790105 / 973284296 : ℝ), (10360658924 / 574343839 : ℝ)] := by
  sorry
