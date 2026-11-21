-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_14
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_14
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:14.587562+00:00
-- url     : https://prove2.me/theorems/f001f718-7da6-44c5-afe6-36462471e9fa
-- title:
--   Rank-cut certificate at D* — certified p-cells on [773/1024, 3133/4096]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [773/1024, 3133/4096]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [773/1024, 3133/4096] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_14 :
    CellOK (773 / 1024 : ℝ) (6205 / 8192 : ℝ) (3733119144 / 712268201 : ℝ) (-205080517 / 69403491 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)] ∧
    CellOK (6205 / 8192 : ℝ) (3113 / 4096 : ℝ) (3733119144 / 712268201 : ℝ) (-205080517 / 69403491 : ℝ) (0 : ℝ)
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]
      ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)] ∧
    CellOK (3113 / 4096 : ℝ) (3133 / 4096 : ℝ) (4998186556 / 929047435 : ℝ) (-3007515572 / 958492055 : ℝ) (0 : ℝ)
      ![(-177513041 / 249401784 : ℝ), (-171087041435 / 441098928259 : ℝ), (-15872702450 / 58239277663 : ℝ), (-133372662731 / 999213921814 : ℝ), (-98006572793 / 734254906204 : ℝ), (-73572416771 / 551196786465 : ℝ), (-128149667404 / 960083791721 : ℝ), (-111676775032 / 836670619535 : ℝ), (-69933123119 / 523931582278 : ℝ)]
      ![(179659328 / 191839589 : ℝ), (40127354 / 78628245 : ℝ), (129297794 / 360558213 : ℝ), (15207931 / 86592636 : ℝ), (114051769 / 649400850 : ℝ), (32104444 / 182799911 : ℝ), (156061485 / 888600518 : ℝ), (100460875 / 572015482 : ℝ), (163948259 / 933507123 : ℝ)] := by
  sorry
