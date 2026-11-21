-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_05
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_05
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:21.233384+00:00
-- url     : https://prove2.me/theorems/4fa4b461-818a-48da-840c-9c364555bda7
-- title:
--   Rank-cut certificate at D* — certified p-cells on [1331/2048, 2765/4096]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [1331/2048, 2765/4096]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [1331/2048, 2765/4096] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_05 :
    CellOK (1331 / 2048 : ℝ) (5427 / 8192 : ℝ) (3973693553 / 795318050 : ℝ) (-757340889 / 288188606 : ℝ) (0 : ℝ)
      ![(1367900903 / 443428466 : ℝ), (2298167923 / 811088051 : ℝ), (1004705489 / 999118486 : ℝ), (-306800278177 / 244097469395 : ℝ), (-609093061519 / 869307113531 : ℝ), (-771572648420 / 782232456067 : ℝ), (601019061 / 703160555 : ℝ), (-609093061519 / 869307113531 : ℝ), (-204728915821 / 292192300508 : ℝ)]
      ![(-3569760181 / 821716360 : ℝ), (-2515279201 / 612531841 : ℝ), (-1288459490 / 888901061 : ℝ), (1123200053 / 580781463 : ℝ), (609729368 / 565554937 : ℝ), (150950296 / 99458311 : ℝ), (-688426050 / 565380503 : ℝ), (609729368 / 565554937 : ℝ), (1068934347 / 991490863 : ℝ)] ∧
    CellOK (5427 / 8192 : ℝ) (2765 / 4096 : ℝ) (3973693553 / 795318050 : ℝ) (-757340889 / 288188606 : ℝ) (0 : ℝ)
      ![(1367900903 / 443428466 : ℝ), (2298167923 / 811088051 : ℝ), (1004705489 / 999118486 : ℝ), (-306800278177 / 244097469395 : ℝ), (-609093061519 / 869307113531 : ℝ), (-771572648420 / 782232456067 : ℝ), (601019061 / 703160555 : ℝ), (-609093061519 / 869307113531 : ℝ), (-204728915821 / 292192300508 : ℝ)]
      ![(-3569760181 / 821716360 : ℝ), (-2515279201 / 612531841 : ℝ), (-1288459490 / 888901061 : ℝ), (1123200053 / 580781463 : ℝ), (609729368 / 565554937 : ℝ), (150950296 / 99458311 : ℝ), (-688426050 / 565380503 : ℝ), (609729368 / 565554937 : ℝ), (1068934347 / 991490863 : ℝ)] := by
  sorry
