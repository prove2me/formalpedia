-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_cumFeasLang_mem_NP
-- name    : ProjSchedTW.Complexity.cumFeasLang_mem_NP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:09:03.462639+00:00
-- url     : https://prove2.me/theorems/d0bf0960-1f9e-4141-a2b4-e58601e36d21
-- title:
--   Proof of Theorem 2.12.1 — feasibility for PSc|temp|C_max is in NP
-- statement:
--   Let $L$ be the language of codes of well-formed instances of $PSc|temp|C_{\max}$ (projects with discrete cumulative resources) that have a feasible schedule, and $L_{\mathrm{acyc}}\subseteq L$ its restriction to instances with an acyclic project network. Then
--   $$L\in\mathrm{NP}\quad\text{and}\quad L_{\mathrm{acyc}}\in\mathrm{NP}.$$
--
--   This is the membership half of Theorem 2.12.1. The book argues it in one sentence: the feasibility of a schedule $S$ can be checked in polynomial time by evaluating the temporal constraints and the inventory constraints at the start and completion times of the activities.
--
--   **Formalization Note** NP is Cook's class from `CookPvsNP_defs`: a polynomial-length certificate over a finite alphabet and a polynomial-time Turing-machine checker. Since schedules are real vectors, a certificate must be a finite object of polynomial size (for example, a schedule with rational start times of polynomial size, or the order of the start and completion events); the book leaves this step implicit. Inventory constraints are required for every $t\ge0$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 130, proof of Theorem 2.12.1, first paragraph (NP membership)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_Cumulative

namespace ProjSchedTW.Complexity

/-- Proof of Theorem 2.12.1 (p. 130): the feasibility problem of `PSc|temp|C_max`, and its
restriction to acyclic project networks, belong to NP. -/
theorem cumFeasLang_mem_NP :
    cumFeasLang (fun _ => True) ∈ CookPvsNP.NP BSym ∧
      cumFeasLang CumInstance.IsAcyclic ∈ CookPvsNP.NP BSym := by sorry

end ProjSchedTW.Complexity
