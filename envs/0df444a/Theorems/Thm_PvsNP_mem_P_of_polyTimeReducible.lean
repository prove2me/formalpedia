-- Prove2me | Theorems.Thm_PvsNP_mem_P_of_polyTimeReducible
-- name    : PvsNP.mem_P_of_polyTimeReducible
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T03:45:58.432481+00:00
-- url     : https://prove2.me/theorems/4c2659f1-5d7a-4f5a-8b76-6119b3d90bcb
-- title:
--   $\mathsf{P}$ is closed downwards under Karp reductions
-- statement:
--   If $L \le_p K$ and $K \in \mathsf{P}$, then $L \in \mathsf{P}$. Composing the polynomial-time reduction with the polynomial-time decision procedure for $K$ gives a polynomial-time decision procedure for $L$; the composition of two polynomial-time computable functions is polynomial-time computable.
-- source:
--   Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Definition 2.7 and the surrounding discussion

import Definitions.Def_PvsNP_reductions

namespace PvsNP

theorem mem_P_of_polyTimeReducible (L K : DecisionProblem)
    (hLK : PolyTimeReducible L K) (hK : K ∈ P) : L ∈ P := by sorry

end PvsNP
