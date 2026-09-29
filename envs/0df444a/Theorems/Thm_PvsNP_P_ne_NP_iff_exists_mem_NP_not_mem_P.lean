-- Prove2me | Theorems.Thm_PvsNP_P_ne_NP_iff_exists_mem_NP_not_mem_P
-- name    : PvsNP.P_ne_NP_iff_exists_mem_NP_not_mem_P
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T03:41:43.869986+00:00
-- url     : https://prove2.me/theorems/8031a1e0-47e5-4777-8df9-aa5130bcb8e3
-- title:
--   $\mathsf{P} \ne \mathsf{NP}$ iff some $\mathsf{NP}$ problem is not in $\mathsf{P}$
-- statement:
--   The two classes differ if and only if there is a witness of the separation: a decision problem that lies in $\mathsf{NP}$ but not in $\mathsf{P}$. The nontrivial direction uses the inclusion $\mathsf{P} \subseteq \mathsf{NP}$, which turns set inequality into strict inclusion.
-- source:
--   Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Chapter 2

import Definitions.Def_PvsNP_complexity_classes

namespace PvsNP

theorem P_ne_NP_iff_exists_mem_NP_not_mem_P :
    P ≠ NP ↔ ∃ L : DecisionProblem, L ∈ NP ∧ L ∉ P := by sorry

end PvsNP
