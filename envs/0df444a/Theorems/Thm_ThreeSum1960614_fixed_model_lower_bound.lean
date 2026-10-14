-- Prove2me | Theorems.Thm_ThreeSum1960614_fixed_model_lower_bound
-- name    : ThreeSum1960614.fixed_model_lower_bound
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:09:31.049867+00:00
-- url     : https://prove2.me/theorems/9319378a-d6f7-45f7-b66b-35f91d017f2e
-- title:
--   Lower bound for the relaxed fixed-expansion cost model
-- statement:
--   For every real tuple $(e,b,S,\theta,\tau,\rho,R)$ satisfying the explicitly defined relaxed twelve-cost model at $c=232$, its common cost upper bound satisfies $R>1.96061349120$. The model requires $0<e<1$, $b<0$, $S>0$, $0\le\theta\le1/2$, $0\le\tau<1$, $\rho>0$, $S-2b\le\gamma_{232}(\theta)$, the whole-interval bound $H(t)\le\rho(1+\gamma_{232}(t))$, and each ledger charge at most $R$. The quantification covers all such parameter choices. This is only a lower bound for that fixed model, not for 3SUM algorithms or other expansions.
-- source:
--   User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md (14 October 2026); Section 7; upstream https://github.com/c0ldzy17/three-sum-lean/tree/2b639655e07421b9ac743de9090459bab473a7c0

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.fixed_model_lower_bound
    (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R) :
    (196061349120 / 100000000000 : ℝ) < R := by sorry
