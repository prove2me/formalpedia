-- Prove2me | Theorems.Thm_ResourceScheduling_Chain_p2_res111_chain_stronglyNPHard
-- name    : ResourceScheduling.Chain.p2_res111_chain_stronglyNPHard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:28:21.224774+00:00
-- url     : https://prove2.me/theorems/de74f080-99c7-4b59-a91e-4685fde86d0d
-- title:
--   Theorem 7 — $P2\mid res111, chain, p_j=1\mid C_{\max}$ is NP-hard in the strong sense
-- statement:
--   Assume that 3-PARTITION (with $\tfrac14 b < a_j < \tfrac12 b$) is NP-hard in the strong sense, i.e. that its language of yes-instances with all numbers written in unary is NP-hard. This is Garey and Johnson's theorem, cited by the paper. Then
--   $$P2\mid res111,\ chain,\ p_j = 1\mid C_{\max} \text{ is NP-hard in the strong sense:}$$
--   the language of unary codes of pairs $(I, y)$, where $I$ is an instance with two identical machines, a single resource of size one, requirements in $\{0,1\}$, acyclic chain-like precedence constraints and unit-time jobs, and some feasible schedule of $I$ has $C_{\max} \le y$, is NP-hard.
--
--   This is the main theorem of the paper. Two identical machines with unit-time jobs are solvable in polynomial time under any resource constraints when there are no precedence constraints (Theorem 1 of the paper); the theorem shows that one unit resource together with chains already makes the problem strongly NP-hard. It dominates the earlier strong NP-hardness results for $P2\mid res1\cdot\cdot, tree, p_j=1\mid C_{\max}$ and $P2\mid res111, prec, p_j=1\mid C_{\max}$.
--
--   **Formalization Note.** The hypothesis is the cited NP-hardness of the source problem, the only fact taken from outside the paper; the reduction and its polynomial running time are what a proof must supply. NP-hardness is with respect to polynomial-time many-one reductions computed by Cook's one-tape Turing machines (`CookPvsNP_defs`). Schedules have real start times and the resource is checked at every real time. Thresholds are natural numbers, which makes the hardness statement stronger.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 18, Theorem 7

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Complexity
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_ResourceScheduling_Chain_Problems

namespace ResourceScheduling.Chain
theorem p2_res111_chain_stronglyNPHard
    (h3P : StronglyNPHard ThreePartition.code ThreePartition.IsYes) :
    StronglyNPHard Instance.decisionCode P2Res111Chain := by sorry
end ResourceScheduling.Chain
