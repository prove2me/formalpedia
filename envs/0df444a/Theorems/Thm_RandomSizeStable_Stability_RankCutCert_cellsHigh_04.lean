-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsHigh_04
-- name    : RandomSizeStable.Stability.RankCutCert.cellsHigh_04
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:12:57.794013+00:00
-- url     : https://prove2.me/theorems/3892b732-0dda-4d8e-8c93-3643f61726cc
-- title:
--   Rank-cut certificate at D* — certified p-cells on [1023/1024, 4095/4096]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients ($l_2 = 0$): for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [1023/1024, 4095/4096]$, near $p = 1$ (the bracket checked as $B/(1-p)$). The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [1023/1024, 4095/4096] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsHigh_04 :
    CellOK (1023 / 1024 : ℝ) (4095 / 4096 : ℝ) (-31249553813 / 157778648 : ℝ) (200 : ℝ) (0 : ℝ)
      ![(102375 / 512 : ℝ), (129305943808 / 686703999 : ℝ), (134976616191 / 715813307 : ℝ), (64793145029 / 340603310 : ℝ), (130995947611 / 691606217 : ℝ), (2274426719 / 11963113 : ℝ), (168376668239 / 886661975 : ℝ), (189749073631 / 991604195 : ℝ), (149851181968 / 770363809 : ℝ)]
      ![(-200 : ℝ), (-135802345294 / 721235255 : ℝ), (-47983470799 / 254567278 : ℝ), (-130827044775 / 688248314 : ℝ), (-82867759424 / 437964221 : ℝ), (-180146942001 / 948748622 : ℝ), (-90487539256 / 477256323 : ℝ), (-178199679481 / 933136053 : ℝ), (-155708900583 / 802698737 : ℝ)] := by
  sorry
