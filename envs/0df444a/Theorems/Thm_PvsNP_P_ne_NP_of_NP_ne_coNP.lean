-- Prove2me | Theorems.Thm_PvsNP_P_ne_NP_of_NP_ne_coNP
-- name    : PvsNP.P_ne_NP_of_NP_ne_coNP
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T04:12:24.02477+00:00
-- url     : https://prove2.me/theorems/da9b41f6-f59e-4fb1-bafe-533ee45c8ea8
-- title:
--   $\mathsf{NP} \ne \mathsf{coNP}$ implies $\mathsf{P} \ne \mathsf{NP}$
-- statement:
--   If $\mathsf{NP} \ne \mathsf{coNP}$ then $\mathsf{P} \ne \mathsf{NP}$. Contrapositively, if $\mathsf{P} = \mathsf{NP}$ then, since $\mathsf{P}$ is closed under complement, $\mathsf{NP}$ is closed under complement as well and $\mathsf{NP} = \mathsf{coNP}$.
-- source:
--   Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Chapter 2.6

import Definitions.Def_PvsNP_complexity_classes

namespace PvsNP

theorem P_ne_NP_of_NP_ne_coNP (h : NP ≠ coNP) : P ≠ NP := by sorry

end PvsNP
