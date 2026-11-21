-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellsMid_06
-- name    : RandomSizeStable.Stability.RankCutCert.cellsMid_06
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:34:18.211625+00:00
-- url     : https://prove2.me/theorems/e495780c-9677-45e7-9599-a85765234cee
-- title:
--   Rank-cut certificate at D* — certified p-cells on [2765/4096, 2867/4096]
-- statement:
--   Each conjunct is `CellOK p0 p1 l0 l1 l2 t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`) for one $p$-cell $[p_0, p_1]$ with explicit rational multiplier coefficients: for every $p \in [p_0,p_1] \cap (0,1)$, $\lambda(p) = (l_0 + l_1 p)/(1-p) + l_2 p/(\mu p - \Phi(p)) \ge 0$, every $\tau_j(p) = p(t_{0,j} + t_{1,j}p) \ge 0$, and for each of the nine families $j$ and all $0 \le a \le p \le A \le 1$ the two cut slacks $G_1, G_2$ are nonnegative. The cells of this statement are consecutive and cover $p \in [2765/4096, 2867/4096]$. The coefficients come from a linear program; the claim is checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), certified p-cells covering [2765/4096, 2867/4096] (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.cellsMid_06 :
    CellOK (2765 / 4096 : ℝ) (11 / 16 : ℝ) (521916569 / 106205649 : ℝ) (-2273421464 / 908419507 : ℝ) (0 : ℝ)
      ![(1588737721 / 512512830 : ℝ), (2183192631 / 934448126 : ℝ), (1539875353 / 972186335 : ℝ), (208130103 / 161435795 : ℝ), (64341894 / 57421841 : ℝ), (617773206 / 642589127 : ℝ), (290478222 / 364283159 : ℝ), (-50465969 / 446091646 : ℝ), (-69738192 / 915396313 : ℝ)]
      ![(-1815933851 / 415427000 : ℝ), (-3313752860 / 995829821 : ℝ), (-2073177495 / 920317097 : ℝ), (-145009977 / 79168291 : ℝ), (-1194597713 / 751033121 : ℝ), (-854002588 / 626441577 : ℝ), (-1073263637 / 950649152 : ℝ), (148891451 / 864438729 : ℝ), (98736601 / 829166731 : ℝ)] ∧
    CellOK (11 / 16 : ℝ) (2867 / 4096 : ℝ) (521916569 / 106205649 : ℝ) (-2273421464 / 908419507 : ℝ) (0 : ℝ)
      ![(1588737721 / 512512830 : ℝ), (2183192631 / 934448126 : ℝ), (1539875353 / 972186335 : ℝ), (208130103 / 161435795 : ℝ), (64341894 / 57421841 : ℝ), (617773206 / 642589127 : ℝ), (290478222 / 364283159 : ℝ), (-50465969 / 446091646 : ℝ), (-69738192 / 915396313 : ℝ)]
      ![(-1815933851 / 415427000 : ℝ), (-3313752860 / 995829821 : ℝ), (-2073177495 / 920317097 : ℝ), (-145009977 / 79168291 : ℝ), (-1194597713 / 751033121 : ℝ), (-854002588 / 626441577 : ℝ), (-1073263637 / 950649152 : ℝ), (148891451 / 864438729 : ℝ), (98736601 / 829166731 : ℝ)] := by
  sorry
