-- Prove2me | Theorems.Thm_PvsNP_P_subset_coNP
-- name    : PvsNP.P_subset_coNP
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T03:38:32.851888+00:00
-- url     : https://prove2.me/theorems/fd37105d-e42c-4720-bf49-9eceefd80e0d
-- title:
--   $\mathsf{P} \subseteq \mathsf{coNP}$
-- statement:
--   Every problem solvable in deterministic polynomial time lies in $\mathsf{coNP}$: its complement is again in $\mathsf{P}$, hence in $\mathsf{NP}$.
-- source:
--   google-deepmind/formal-conjectures, FormalConjectures/Millennium/PvsNP.lean and FormalConjecturesForMathlib/Computability/Complexity.lean, https://github.com/google-deepmind/formal-conjectures

import Definitions.Def_PvsNP_complexity_classes

namespace PvsNP

theorem P_subset_coNP : P ⊆ coNP := by sorry

end PvsNP
