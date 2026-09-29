-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_p3_res11_stronglyNPHard
-- name    : ResourceScheduling.Graph.p3_res11_stronglyNPHard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:33:26.782978+00:00
-- url     : https://prove2.me/theorems/1d9b5c26-288b-4388-879d-e134442c5510
-- title:
--   Theorem 2 — P3 | res·11, p_j = 1 | C_max is NP-hard in the strong sense
-- statement:
--   Assume that PARTITION INTO TRIANGLES is NP-hard (Garey and Johnson, problem GT11, the NP-completeness result the paper cites as [5]). Then the decision version of
--   $$P3\,|\,res{\cdot}11,\,p_j=1\,|\,C_{\max}$$
--   is NP-hard in the strong sense: given three identical machines, $n$ unit-time jobs, $l$ resources of size $1$ (with $l$ part of the input) and requirements $r_{hj}\in\{0,1\}$, and a threshold $y$, deciding whether a feasible schedule with $C_{\max}\le y$ exists is NP-hard even when all numbers are written in unary.
--
--   Together with Theorem 1 (two identical machines are polynomially solvable under any resource constraints), this shows that three identical machines already make the problem hard once the number of unit resources is part of the input.
--
--   **Formalization Note.** The cited NP-hardness of PARTITION INTO TRIANGLES is the only hypothesis; it concerns the language of codes of yes-instances (unary $t$ followed by the adjacency matrix). Strong NP-hardness is NP-hardness of the language of unary codes of yes-instances, which is equivalent to Garey and Johnson's definition.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, Theorem 2

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction

namespace ResourceScheduling.Graph

/-- Theorem 2, p. 15: `P3 | res·11, p_j = 1 | C_max` is NP-hard in the strong sense, given that
PARTITION INTO TRIANGLES is NP-hard (Garey & Johnson 1979, GT11, cited by the paper). -/
theorem p3_res11_stronglyNPHard (hT : NPHard trianglesLang) :
    StronglyNPHard P3Yes encP3 := by sorry

end ResourceScheduling.Graph
