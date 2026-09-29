-- Prove2me | Theorems.Thm_PvsNP_P_ne_NP_millennium
-- name    : PvsNP.P_ne_NP_millennium
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T03:31:45.090592+00:00
-- url     : https://prove2.me/theorems/31a50e95-7f44-43e6-9c28-50f4610c062a
-- title:
--   $\mathsf{P} \ne \mathsf{NP}$
-- statement:
--   The complexity classes $\mathsf{P}$ and $\mathsf{NP}$ are different: there is a decision problem whose solutions can be verified in polynomial time but which cannot be solved in polynomial time by a deterministic Turing machine. This is the Clay Mathematics Institute Millennium Prize Problem, open since it was posed by Cook (1971) and Levin (1973).
-- source:
--   Clay Mathematics Institute, P vs NP problem, https://www.claymath.org/millennium/p-vs-np/; google-deepmind/formal-conjectures, FormalConjectures/Millennium/PvsNP.lean and FormalConjecturesForMathlib/Computability/Complexity.lean, https://github.com/google-deepmind/formal-conjectures

import Definitions.Def_PvsNP_complexity_classes

namespace PvsNP

theorem P_ne_NP_millennium : P ≠ NP := by sorry

end PvsNP
