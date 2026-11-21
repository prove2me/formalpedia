-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsHigh_03
-- name    : RandomSizeStable.Stability.RankCutCert.cellsHigh_03
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:12:57.696878+00:00
-- url     : https://prove2.me/theorems/69a5c25c-fdff-4b65-b408-e92a046e2b6b
-- title:
--   Rank-cut certificate at D* — certified p-cells on [2043/2048, 1023/1024]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients ($l_2 = 0$): for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [2043/2048, 1023/1024]$, near $p = 1$ (the bracket checked as $B/(1-p)$). The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [2043/2048, 1023/1024] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsHigh_03 :
    CellOK (2043 / 2048 : ℝ) (1023 / 1024 : ℝ) (-151576125105 / 765871472 : ℝ) (200 : ℝ) (0 : ℝ)
      ![(25575 / 128 : ℝ), (191119738936 / 989858505 : ℝ), (78688697228 / 407099909 : ℝ), (38447452333 / 197967376 : ℝ), (183794254351 / 948052457 : ℝ), (151042896333 / 777465601 : ℝ), (132170595567 / 680458709 : ℝ), (200 : ℝ), (200 : ℝ)]
      ![(-200 : ℝ), (-71919501894 / 372229475 : ℝ), (-147884328238 / 764812215 : ℝ), (-58859150707 / 303068019 : ℝ), (-159916392197 / 825113653 : ℝ), (-1871848353 / 9639859 : ℝ), (-62014434829 / 319528804 : ℝ), (-155488164083 / 778368812 : ℝ), (-189058553466 / 947133625 : ℝ)] := by
  sorry
