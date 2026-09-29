-- Prove2me | Theorems.Thm_PvsNP_coP_eq_P
-- name    : PvsNP.coP_eq_P
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T03:35:46.722699+00:00
-- url     : https://prove2.me/theorems/cbe97172-f2df-4414-9667-b206085eec9b
-- title:
--   $\mathsf{P}$ is closed under complement
-- statement:
--   The class of decision problems whose complement lies in $\mathsf{P}$ is exactly $\mathsf{P}$: $\mathsf{coP} = \mathsf{P}$. Equivalently, $L \in \mathsf{P}$ if and only if $L^{\mathrm{c}} \in \mathsf{P}$, since Boolean negation is computable in polynomial time and polynomial-time computable maps compose.
-- source:
--   google-deepmind/formal-conjectures, FormalConjectures/Millennium/PvsNP.lean and FormalConjecturesForMathlib/Computability/Complexity.lean, https://github.com/google-deepmind/formal-conjectures

import Definitions.Def_PvsNP_complexity_classes

namespace PvsNP

theorem coP_eq_P : { L : DecisionProblem | Lᶜ ∈ P } = P := by sorry

end PvsNP
