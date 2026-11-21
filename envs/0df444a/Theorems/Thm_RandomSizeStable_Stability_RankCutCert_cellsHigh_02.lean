-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsHigh_02
-- name    : RandomSizeStable.Stability.RankCutCert.cellsHigh_02
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:13:09.917531+00:00
-- url     : https://prove2.me/theorems/4914936e-a717-478b-9eda-57658add2627
-- title:
--   Rank-cut certificate at D* — certified p-cells on [1019/1024, 2043/2048]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients ($l_2 = 0$): for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [1019/1024, 2043/2048]$, near $p = 1$ (the bracket checked as $B/(1-p)$). The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [1019/1024, 2043/2048] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsHigh_02 :
    CellOK (1019 / 1024 : ℝ) (2043 / 2048 : ℝ) (-177108805448 / 896204925 : ℝ) (200 : ℝ) (0 : ℝ)
      ![(1995117187501 / 10000000000 : ℝ), (16428429981 / 83845198 : ℝ), (183228014682 / 934187837 : ℝ), (192157981351 / 976589465 : ℝ), (175296076895 / 891575588 : ℝ), (60323183711 / 306351223 : ℝ), (137239363018 / 696829311 : ℝ), (23358919411 / 118246519 : ℝ), (121039140128 / 607184185 : ℝ)]
      ![(-200 : ℝ), (-119705238487 / 609609003 : ℝ), (-39561302514 / 201332777 : ℝ), (-63689820499 / 323206258 : ℝ), (-184595653402 / 937738719 : ℝ), (-43012916203 / 218226023 : ℝ), (-167473940442 / 849760295 : ℝ), (-97418355745 / 493024203 : ℝ), (-17726278270 / 88966107 : ℝ)] := by
  sorry
