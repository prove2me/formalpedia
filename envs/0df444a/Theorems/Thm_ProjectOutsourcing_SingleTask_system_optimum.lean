-- Prove2me | Theorems.Thm_ProjectOutsourcing_SingleTask_system_optimum
-- name    : ProjectOutsourcing.SingleTask.system_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:02.755013+00:00
-- url     : https://prove2.me/theorems/19c37f6a-561c-42cd-9160-9d0e938003e9
-- title:
--   §3, p. 8, (2) — under Assumptions 1–2, Π is concave on [0, ∞), the optimal work rate r* is unique, and it satisfies the first-order condition (2)
-- statement:
--   Under the standing assumptions of Section 3 (Assumptions 1–2), consider the system profit
--   $$\Pi(r)=Q\,\mathbb E_Z[e^{-\alpha Z/r}]-c(r),\qquad r\ge 0 .$$
--   Then
--
--   1. $\Pi$ is concave on $[0,\infty)$;
--   2. there is exactly one $r^*\ge 0$ maximizing $\Pi$ on $[0,\infty)$;
--   3. $\Pi$ is differentiable at $r^*$, and
--   $$\Pi'(r^*)=Q\frac{\alpha}{(r^*)^2}\,\mathbb E_Z\big[Ze^{-\alpha Z/r^*}\big]-c'(r^*)=0. \tag{2}$$
--
--   The optimal system profit $\Pi^*=\Pi(r^*)$ is the benchmark that every contract form in the mission is measured against. This statement supplies existence and uniqueness of the system-optimal rate $r^*$, which the other statements take as given.
--
--   **Formalization Note** Differentiability at $r^*$ implies $r^*>0$: at $r=0$ the discounted reward is set to $0$ and is not differentiable. The page does not state $r^*>0$, but it is implicit in the first-order condition (2), since $c'(0)=0$ while the marginal reward at $0$ is positive.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), p. 8, §3, (1)–(2)

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

namespace ProjectOutsourcing.SingleTask

theorem system_optimum (M : Model) (hM : M.Valid) :
    ConcaveOn ℝ (Set.Ici 0) (sysProfit M) ∧ (∃! r, IsSystemOpt M r) ∧
      ∀ r, IsSystemOpt M r →
        HasDerivAt (sysProfit M)
            (M.Q * (M.alpha / r ^ 2) * discZ M M.alpha r - deriv M.c r) r ∧
          M.Q * (M.alpha / r ^ 2) * discZ M M.alpha r - deriv M.c r = 0 := by sorry

end ProjectOutsourcing.SingleTask
