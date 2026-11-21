-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_08
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_08
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:21.84885+00:00
-- url     : https://prove2.me/theorems/22e02e7e-5dd0-454c-ae73-2ed85f3563c8
-- title:
--   Rank-cut certificate at D* — certified p-cells on [2949/4096, 3031/4096]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [2949/4096, 3031/4096]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [2949/4096, 3031/4096] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_08 :
    CellOK (2949 / 4096 : ℝ) (1485 / 2048 : ℝ) (2266790737 / 457512305 : ℝ) (-424132787 / 165479401 : ℝ) (0 : ℝ)
      ![(22684642 / 72872367 : ℝ), (919831348 / 965653237 : ℝ), (22684642 / 72872367 : ℝ), (527437836712 / 944539609035 : ℝ), (275425921 / 555236326 : ℝ), (107549287 / 345492387 : ℝ), (297834278 / 956765763 : ℝ), (165738626 / 513449787 : ℝ), (269156759 / 864641819 : ℝ)]
      ![(-158324779 / 368787624 : ℝ), (-76088715 / 57920159 : ℝ), (-158324779 / 368787624 : ℝ), (-761003435 / 988170789 : ℝ), (-298092917 / 435733770 : ℝ), (-251547395 / 585932074 : ℝ), (-51882583 / 120850663 : ℝ), (-364280645 / 818289243 : ℝ), (-364944315 / 850068749 : ℝ)] ∧
    CellOK (1485 / 2048 : ℝ) (1495 / 2048 : ℝ) (1303961251 / 257020496 : ℝ) (-543673036 / 199340413 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (-2154 / 233026039 : ℝ), (0 : ℝ), (0 : ℝ), (201554221 / 987192551 : ℝ), (88218127 / 497158998 : ℝ), (0 : ℝ), (132356580466 / 912596729391 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (4807 / 377076422 : ℝ), (0 : ℝ), (0 : ℝ), (-194168574 / 694224847 : ℝ), (-95984201 / 394864841 : ℝ), (0 : ℝ), (-192609731 / 969444241 : ℝ)] ∧
    CellOK (1495 / 2048 : ℝ) (3011 / 4096 : ℝ) (4891231661 / 965006759 : ℝ) (-441632419 / 162276072 : ℝ) (0 : ℝ)
      ![(614625814983 / 774331095484 : ℝ), (188835467 / 436565150 : ℝ), (124033445 / 408084897 : ℝ), (9267385 / 65412722 : ℝ), (66539105 / 295394578 : ℝ), (154999248 / 778901369 : ℝ), (64519338322 / 373052779239 : ℝ), (136308929 / 929931700 : ℝ), (137735366 / 972188509 : ℝ)]
      ![(-481730769 / 446139932 : ℝ), (-131390077 / 223294935 : ℝ), (-205262887 / 496447075 : ℝ), (-135649814 / 703841753 : ℝ), (-69341040 / 226290709 : ℝ), (-139827600 / 516531233 : ℝ), (-71043301 / 301963406 : ℝ), (-98950138 / 496242503 : ℝ), (-183883718 / 954111433 : ℝ)] ∧
    CellOK (3011 / 4096 : ℝ) (3031 / 4096 : ℝ) (4013440267 / 774310427 : ℝ) (-795009686 / 276310609 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)] := by
  sorry
