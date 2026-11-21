-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_16
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_16
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:32.068704+00:00
-- url     : https://prove2.me/theorems/c771f4c4-c18b-454a-9a65-83d2514ddb39
-- title:
--   Rank-cut certificate at D* — certified p-cells on [809/1024, 1741/2048]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [809/1024, 1741/2048]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [809/1024, 1741/2048] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_16 :
    CellOK (809 / 1024 : ℝ) (407 / 512 : ℝ) (3758486008 / 695417517 : ℝ) (-2974772843 / 938223376 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (-2929 / 993699330 : ℝ), (0 : ℝ), (0 : ℝ), (-1286382 / 838096333921 : ℝ), (-758451 / 559348019966 : ℝ), (0 : ℝ), (0 : ℝ), (31099688 / 29250261 : ℝ)]
      ![(0 : ℝ), (1019 / 273123063 : ℝ), (0 : ℝ), (0 : ℝ), (1639 / 843574049 : ℝ), (1692 / 985760639 : ℝ), (0 : ℝ), (0 : ℝ), (-785634857 / 587379663 : ℝ)] ∧
    CellOK (407 / 512 : ℝ) (3277 / 4096 : ℝ) (402031981 / 74802935 : ℝ) (-334639708 / 106765593 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)] ∧
    CellOK (3277 / 4096 : ℝ) (3379 / 4096 : ℝ) (5025750230 / 928948313 : ℝ) (-2179908949 / 685289336 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)] ∧
    CellOK (3379 / 4096 : ℝ) (1741 / 2048 : ℝ) (2827766351 / 511307539 : ℝ) (-3291210067 / 984442565 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (514428250084 / 486500625689 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-674622991 / 542361121 : ℝ)] := by
  sorry
