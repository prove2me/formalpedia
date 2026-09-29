-- Prove2me | Theorems.Thm_PvsNP_P_subset_NP_millennium
-- name    : PvsNP.P_subset_NP_millennium
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T03:32:53.98902+00:00
-- url     : https://prove2.me/theorems/6001690a-7071-4210-b891-ecd6a20d4e40
-- title:
--   $\mathsf{P} \subseteq \mathsf{NP}$
-- statement:
--   Every problem solvable in deterministic polynomial time is also verifiable in polynomial time. Given $L \in \mathsf{P}$, take the zero polynomial as the witness bound and the verifier $R(x, w) = L(x)$, which ignores its witness.
-- source:
--   Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Chapter 2; google-deepmind/formal-conjectures, FormalConjectures/Millennium/PvsNP.lean and FormalConjecturesForMathlib/Computability/Complexity.lean, https://github.com/google-deepmind/formal-conjectures

import Definitions.Def_PvsNP_complexity_classes

namespace PvsNP

theorem P_subset_NP_millennium : P ⊆ NP := by sorry

end PvsNP
