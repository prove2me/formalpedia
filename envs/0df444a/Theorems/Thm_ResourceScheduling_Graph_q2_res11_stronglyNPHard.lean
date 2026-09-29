-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_q2_res11_stronglyNPHard
-- name    : ResourceScheduling.Graph.q2_res11_stronglyNPHard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:36:25.177137+00:00
-- url     : https://prove2.me/theorems/e7364bce-7265-4419-a679-240587aaea36
-- title:
--   Theorem 3 — Q2 | res·11, p_j = 1 | C_max is NP-hard in the strong sense
-- statement:
--   Assume that PARTITION INTO PATHS OF LENGTH 2 is NP-hard (Garey and Johnson, problem GT13, the NP-completeness result the paper cites as [5]). Then the decision version of
--   $$Q2\,|\,res{\cdot}11,\,p_j=1\,|\,C_{\max}$$
--   is NP-hard in the strong sense: given two uniform machines with positive integer speeds $q_1,q_2$, $n$ unit-time jobs (processing time $1/q_i$ on machine $M_i$), $l$ resources of size $1$ (with $l$ part of the input) and requirements $r_{hj}\in\{0,1\}$, and a threshold $y$, deciding whether a feasible schedule with $C_{\max}\le y$ exists is NP-hard even when all numbers are written in unary.
--
--   Two identical machines are polynomially solvable under any resource constraints (Theorem 1); this theorem shows that two machines of different speeds already make the problem hard once the number of unit resources is part of the input.
--
--   **Formalization Note.** The cited NP-hardness of PARTITION INTO PATHS OF LENGTH 2 is the only hypothesis; it concerns the language of codes of yes-instances (unary $t$ followed by the adjacency matrix). The speeds range over all positive integers, in either order. Strong NP-hardness is NP-hardness of the language of unary codes of yes-instances, which is equivalent to Garey and Johnson's definition.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, Theorem 3

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph

/-- Theorem 3, p. 15: `Q2 | res·11, p_j = 1 | C_max` is NP-hard in the strong sense, given that
PARTITION INTO PATHS OF LENGTH 2 is NP-hard (Garey & Johnson 1979, GT13, cited by the paper). -/
theorem q2_res11_stronglyNPHard (hP : NPHard pathsLang) :
    StronglyNPHard Q2Yes encQ2 := by sorry

end ResourceScheduling.Graph
