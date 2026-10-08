-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_limitCircle_of_sqIntegrable
-- name    : TeschlQM.SturmLiouville.limitCircle_of_sqIntegrable
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-10-04T19:57:08.655513+00:00
-- url     : https://prove2.me/theorems/4e8c7cd5-05e1-4300-bb95-d18b3bd2ccbc
-- title:
--   All solutions square integrable near $a$ for a real $\lambda$ implies limit circle at $a$
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data and $\lambda\in\mathbb R$. If every solution of $(\tau-\lambda)u=0$ is square integrable near $a$, then $\tau$ is limit circle at $a$ in the Wronskian sense of Teschl p. 187: there is $v\in\mathfrak D(\tau)$ with $W_a(v^*,v)=0$ and $W_a(v,f)\neq0$ for some $f\in\mathfrak D(\tau)$. Similarly at $b$.
--
--   Proof idea: take a real fundamental system $u_1,u_2$ of $(\tau-\lambda)u=0$ with $W(u_1,u_2)=1$. Modify $u_1,u_2$ away from $a$ so that they belong to the maximal domain $\mathfrak D(\tau)$ and vanish near $b$. Then $v=\tilde u_1$ is real, so $W_a(v^*,v)=0$, and $W_a(\tilde u_1,\tilde u_2)=1$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, Section 9.2, proof of Theorem 9.9 (p. 191), the 'if' direction

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle
import Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear

namespace TeschlQM.SturmLiouville

theorem limitCircle_of_sqIntegrable (L : SLData) (lam : ℝ) :
    ((∀ u : ℝ → ℂ, IsSolution L lam 0 u → IsSqIntegrableNearLeft L u) → IsLimitCircleLeft L) ∧
    ((∀ u : ℝ → ℂ, IsSolution L lam 0 u → IsSqIntegrableNearRight L u) →
      IsLimitCircleRight L) := by sorry

end TeschlQM.SturmLiouville
