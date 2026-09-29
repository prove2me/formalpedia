-- Prove2me | Theorems.Thm_ResourceScheduling_Chain_p3_res1_stronglyNPHard
-- name    : ResourceScheduling.Chain.p3_res1_stronglyNPHard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:26:32.856994+00:00
-- url     : https://prove2.me/theorems/334efce6-3380-4849-a56c-0ad736f1e151
-- title:
--   Theorem 4 (Garey & Johnson) — $P3\mid res1\cdot\cdot, p_j=1\mid C_{\max}$ is NP-hard in the strong sense
-- statement:
--   Assume that 3-PARTITION (with $\tfrac14 b < a_j < \tfrac12 b$) is NP-hard in the strong sense, i.e. that its language of yes-instances with all numbers written in unary is NP-hard. This is Garey and Johnson's theorem, cited by the paper as "the first number problem proved to be NP-complete in the strong sense". Then
--   $$P3\mid res1\cdot\cdot,\ p_j = 1\mid C_{\max} \text{ is NP-hard in the strong sense:}$$
--   the language of unary codes of pairs $(I, y)$, where $I$ is an instance with three identical machines, one resource of positive size, arbitrary requirements, no precedence constraints and unit-time jobs, and some feasible schedule of $I$ has $C_{\max} \le y$, is NP-hard.
--
--   This is Theorem 4 of the paper, originally due to Garey and Johnson (1975). It shows that one resource already makes unit-time scheduling on three machines hard, in contrast with two machines (Theorem 1 of the paper).
--
--   **Formalization Note.** The hypothesis is the cited NP-hardness of the source problem, the only fact taken from outside the paper; the reduction and its polynomial running time are what a proof must supply. NP-hardness is with respect to polynomial-time many-one reductions computed by Cook's one-tape Turing machines (`CookPvsNP_defs`). Thresholds are natural numbers.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 16, Theorem 4

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Complexity
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_ResourceScheduling_Chain_Problems

namespace ResourceScheduling.Chain
theorem p3_res1_stronglyNPHard
    (h3P : StronglyNPHard ThreePartition.code ThreePartition.IsYes) :
    StronglyNPHard Instance.decisionCode P3Res1 := by sorry
end ResourceScheduling.Chain
