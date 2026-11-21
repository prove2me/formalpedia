-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_p1_ok
-- name    : RandomSizeStable.Stability.RankCutCert.p1_ok
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T18:12:52.430924+00:00
-- url     : https://prove2.me/theorems/43c542e1-86e0-49a4-acb5-6012613dde9c
-- title:
--   Rank-cut certificate at D* — the cut inequality at p = 1
-- statement:
--   For the explicit rational vectors $t_0, t_1$ in the statement: every $t_{0,j} + t_{1,j} \ge 0$, and `P1OK t0 t1` (bundle `RandomSizeStable_Stability_RankCutCert`): for each of the nine families $j$ and every $0 \le a \le 1$, $a + (t_{0,j} + t_{1,j})(\mu - \phi(\rho_j(a))) \le$ `tail j a`. This is the case $p = 1$ of the cut inequality, where $\lambda(1) = 0$ and $\tau_j(1) = t_{0,j} + t_{1,j}$. Checked by evaluating first-order Taylor models in the kernel.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), the cut inequality at p = 1 for explicit multipliers (computation, not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert

theorem RandomSizeStable.Stability.RankCutCert.p1_ok :
    (∀ j, 0 ≤ (![(21663339783 / 965139899 : ℝ), (-15507027803 / 764280335 : ℝ), (26793293213 / 962943567 : ℝ), (3238867408 / 779553387 : ℝ), (-7659622881 / 430143641 : ℝ), (-15846098066 / 998377629 : ℝ), (-14063250055 / 837429942 : ℝ), (20479612538 / 926226839 : ℝ), (5832627885 / 419285366 : ℝ)] : Fin 9 → ℝ) j + (![(-7544500551 / 366812365 : ℝ), (18381505213 / 826668022 : ℝ), (-25378588681 / 982957904 : ℝ), (-1699605521 / 818048862 : ℝ), (15083534241 / 756360991 : ℝ), (6078045133 / 336704227 : ℝ), (72000963 / 3783241 : ℝ), (-13634424092 / 688972377 : ℝ), (-6976000790 / 610025481 : ℝ)] : Fin 9 → ℝ) j) ∧
      P1OK ![(21663339783 / 965139899 : ℝ), (-15507027803 / 764280335 : ℝ), (26793293213 / 962943567 : ℝ), (3238867408 / 779553387 : ℝ), (-7659622881 / 430143641 : ℝ), (-15846098066 / 998377629 : ℝ), (-14063250055 / 837429942 : ℝ), (20479612538 / 926226839 : ℝ), (5832627885 / 419285366 : ℝ)]
        ![(-7544500551 / 366812365 : ℝ), (18381505213 / 826668022 : ℝ), (-25378588681 / 982957904 : ℝ), (-1699605521 / 818048862 : ℝ), (15083534241 / 756360991 : ℝ), (6078045133 / 336704227 : ℝ), (72000963 / 3783241 : ℝ), (-13634424092 / 688972377 : ℝ), (-6976000790 / 610025481 : ℝ)] := by
  sorry
