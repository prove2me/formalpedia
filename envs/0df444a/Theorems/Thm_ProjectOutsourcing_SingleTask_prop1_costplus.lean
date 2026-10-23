-- Prove2me | Theorems.Thm_ProjectOutsourcing_SingleTask_prop1_costplus
-- name    : ProjectOutsourcing.SingleTask.prop1_costplus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:09.378639+00:00
-- url     : https://prove2.me/theorems/3fe75355-f40c-41ea-b4d0-5cfc0c18e123
-- title:
--   Proposition 1 (C+), p. 11, restated p. 12 — Φ^C+ = {0}, with negotiated terms p = 0, β = 1
-- statement:
--   Under the standing assumptions of Section 3,
--
--   1. $\Phi^{C+}=\{0\}$: the cost-plus contract coordinates the system exactly when the client has full bargaining power, $\theta=0$;
--   2. at $\theta=0$ every solution of Problem B (3) under C+ has the terms
--   $$\hat p^{C+}=0,\qquad \hat\beta^{C+}=1 ,$$
--   that is, the client covers all of the subcontractor's cost and pays nothing more.
--
--   The cost-plus contract is one of the two most common contract forms in practice; this statement says that it coordinates the project only in the extreme case where the client has all the bargaining power.
--
--   **Formalization Note** The second coordinate of a C+ term is a dummy fixed at the printed value $\hat\beta^{C+}=1$ (C+ is CS with $\beta=1$). Under C+ with $p=0$ the subcontractor is indifferent among work rates; footnote 1's tie-break (he chooses the system-optimal rate) is part of the model, and it is what makes coordination at $\theta=0$ possible. For $\theta>0$ every feasible C+ outcome gives the subcontractor zero profit, so every feasible outcome solves Problem B, including non-coordinating ones; this is why $\theta>0$ is excluded.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), p. 11, Proposition 1 (part C+); restatement p. 12; footnote 1, p. 12

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

namespace ProjectOutsourcing.SingleTask

theorem prop1_costplus (M : Model) (hM : M.Valid) :
    Phi M .Cplus = {0} ∧ (∀ x, IsNashSol M .Cplus 0 x → x.1 = (0, 1)) := by sorry

end ProjectOutsourcing.SingleTask
