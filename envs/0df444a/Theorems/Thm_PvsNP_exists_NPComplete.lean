-- Prove2me | Theorems.Thm_PvsNP_exists_NPComplete
-- name    : PvsNP.exists_NPComplete
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T03:54:36.346107+00:00
-- url     : https://prove2.me/theorems/23a78933-b941-4308-b934-3b8380e844e1
-- title:
--   Existence of an $\mathsf{NP}$-complete problem (Cook–Levin)
-- statement:
--   There exists an $\mathsf{NP}$-complete decision problem: a problem in $\mathsf{NP}$ to which every problem in $\mathsf{NP}$ reduces by a polynomial-time many-one reduction. This is the existence form of the Cook–Levin theorem, whose classical statement exhibits such a problem explicitly, namely Boolean satisfiability (SAT).
-- source:
--   Stephen A. Cook, The complexity of theorem-proving procedures, STOC 1971, pp. 151-158, https://doi.org/10.1145/800157.805047; Leonid Levin, Universal sequential search problems, Probl. Peredachi Inf. 9(3), 1973; Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Theorem 2.10

import Definitions.Def_PvsNP_reductions

namespace PvsNP

theorem exists_NPComplete : ∃ L : DecisionProblem, NPComplete L := by sorry

end PvsNP
