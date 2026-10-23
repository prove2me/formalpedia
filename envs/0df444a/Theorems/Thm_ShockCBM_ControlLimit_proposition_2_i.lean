-- Prove2me | Theorems.Thm_ShockCBM_ControlLimit_proposition_2_i
-- name    : ShockCBM.ControlLimit.proposition_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:39.04515+00:00
-- url     : https://prove2.me/theorems/79b28fff-3826-430a-8512-04b725adbc7d
-- title:
--   Proposition 2(i), p. 14 — the next-period damage Z(s) is stochastically decreasing in the age t
-- statement:
--   Consider the shock degradation model under its standing assumptions, and for a state $s=(x,n,t)$ let $Z(s)$ be the next period's damage under the predictive law at the state's hyperparameters $(\alpha_0+n,\beta_0+t,a_0+x,b_0+n)$. Then $Z(s)$ is stochastically decreasing in $t$ in the usual stochastic order: for all $x,n\in\mathbb N$, all $t\le t'$ and every threshold $m\in\mathbb N$,
--   $$\mathbb P\big[Z(x,n,t')\ge m\big]\le\mathbb P\big[Z(x,n,t)\ge m\big].$$
--
--   An older component that has sustained the same damage and the same number of shocks is expected to accumulate less damage in the next period.
--
--   **Formalization Note** The usual stochastic order of the paper's Definition 1 ($\mathbb P[X\ge u]\ge\mathbb P[Y\ge u]$ for all real $u$) is stated through tail sums of the pmf at integer thresholds, which is equivalent for $\mathbb N$-valued variables.
-- source:
--   Drent, Drent, Arts, Kapodistria, Real-Time Integrated Learning and Decision Making for Cumulative Shock Degradation, Manufacturing & Service Operations Management 25(1) (2023), doi:10.1287/msom.2022.1149, accepted manuscript, p. 14, Proposition 2(i) (Definition 1, p. 31, (17))

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

namespace ShockCBM.ControlLimit

theorem proposition_2_i (M : Model) (hM : M.Standing) (x n t t' : ℕ) (htt : t ≤ t') (m : ℕ) :
    M.tailZ (x, n, t') m ≤ M.tailZ (x, n, t) m := by sorry

end ShockCBM.ControlLimit
