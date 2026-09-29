-- Prove2me | Theorems.Thm_PvsNP_mem_P_iff_P_eq_NP_of_NPComplete
-- name    : PvsNP.mem_P_iff_P_eq_NP_of_NPComplete
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T03:48:59.077764+00:00
-- url     : https://prove2.me/theorems/483f16a6-6e7a-4c2a-9732-e933c280c2e8
-- title:
--   An $\mathsf{NP}$-complete problem is in $\mathsf{P}$ iff $\mathsf{P} = \mathsf{NP}$
-- statement:
--   For an $\mathsf{NP}$-complete problem $L$: $L \in \mathsf{P}$ if and only if $\mathsf{P} = \mathsf{NP}$. If $L$ is decidable in polynomial time then every $K \in \mathsf{NP}$ reduces to $L$ and is therefore in $\mathsf{P}$, giving $\mathsf{NP} \subseteq \mathsf{P}$; conversely if the classes coincide then $L \in \mathsf{NP} = \mathsf{P}$.
-- source:
--   Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Theorem 2.8 / Definition 2.7

import Definitions.Def_PvsNP_reductions

namespace PvsNP

theorem mem_P_iff_P_eq_NP_of_NPComplete (L : DecisionProblem) (hL : NPComplete L) :
    L ∈ P ↔ P = NP := by sorry

end PvsNP
