-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_17
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_17
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:19.393794+00:00
-- url     : https://prove2.me/theorems/b1e0144c-6023-4ce4-bdc8-fadd9186bc5e
-- title:
--   Rank-cut certificate at D* — certified p-cells on [1741/2048, 3789/4096]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [1741/2048, 3789/4096]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [1741/2048, 3789/4096] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_17 :
    CellOK (1741 / 2048 : ℝ) (7 / 8 : ℝ) (147128402 / 25453127 : ℝ) (-3528617117 / 962868603 : ℝ) (0 : ℝ)
      ![(-1977395 / 455495055492 : ℝ), (31061 / 134234687081 : ℝ), (31061 / 134234687081 : ℝ), (-1077277 / 776827171294 : ℝ), (-260939 / 211818596572 : ℝ), (-1069050 / 982324761053 : ℝ), (-812 / 746059129 : ℝ), (-479893346352 / 878746107821 : ℝ), (-3196766200979 / 942311861456 : ℝ)]
      ![(4026 / 788356805 : ℝ), (-263 / 994949069 : ℝ), (-263 / 994949069 : ℝ), (707 / 433365103 : ℝ), (749 / 516821386 : ℝ), (984 / 768565855 : ℝ), (1011 / 789654644 : ℝ), (409958365 / 638156588 : ℝ), (289713557 / 72597459 : ℝ)] ∧
    CellOK (7 / 8 : ℝ) (1843 / 2048 : ℝ) (3735650849 / 606164358 : ℝ) (-1702406902 / 411022323 : ℝ) (0 : ℝ)
      ![(-335 / 882502529 : ℝ), (17763 / 874684729507 : ℝ), (17599 / 866611650218 : ℝ), (-113522 / 936903471509 : ℝ), (5325 / 262213500998 : ℝ), (-85169 / 791344148899 : ℝ), (-220414423461 / 743044317479 : ℝ), (9591 / 472280129491 : ℝ), (146 / 146014259205 : ℝ)]
      ![(373 / 859781379 : ℝ), (-19 / 846112373 : ℝ), (-16 / 712517831 : ℝ), (89 / 642176777 : ℝ), (-21 / 935177284 : ℝ), (123 / 999064843 : ℝ), (223369946 / 658881781 : ℝ), (-17 / 757048883 : ℝ), (-1 / 1000000000 : ℝ)] ∧
    CellOK (1843 / 2048 : ℝ) (3789 / 4096 : ℝ) (8801811587 / 906432548 : ℝ) (-1420137527 / 174439717 : ℝ) (0 : ℝ)
      ![(-690660846 / 911598325 : ℝ), (-730624629611 / 964346238102 : ℝ), (-2073248921 / 861295675 : ℝ), (-712071154888 / 939857639131 : ℝ), (-1778356739213 / 648477892763 : ℝ), (-346907138 / 925401389 : ℝ), (228583773 / 686687035 : ℝ), (-520843062 / 687457043 : ℝ), (-744320434451 / 982422556402 : ℝ)]
      ![(193302121 / 229599366 : ℝ), (736095377 / 874315455 : ℝ), (107431225 / 40163054 : ℝ), (141161605 / 167668181 : ℝ), (2494999085 / 818732563 : ℝ), (58903701 / 140603899 : ℝ), (-333757515 / 927489841 : ℝ), (161965160 / 192378117 : ℝ), (674639447 / 801319105 : ℝ)] := by
  sorry
