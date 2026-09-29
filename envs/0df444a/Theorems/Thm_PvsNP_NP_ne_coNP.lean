-- Prove2me | Theorems.Thm_PvsNP_NP_ne_coNP
-- name    : PvsNP.NP_ne_coNP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T04:00:06.309872+00:00
-- url     : https://prove2.me/theorems/44c371d5-6501-4a3d-a78c-fa62c98d1d97
-- title:
--   $\mathsf{NP} \ne \mathsf{coNP}$
-- statement:
--   The classes $\mathsf{NP}$ and $\mathsf{coNP}$ are different: some problem has polynomial-size certificates for its yes-instances but not for its no-instances. This is an open conjecture, strictly stronger than $\mathsf{P} \ne \mathsf{NP}$.
-- source:
--   google-deepmind/formal-conjectures, FormalConjectures/Millennium/PvsNP.lean and FormalConjecturesForMathlib/Computability/Complexity.lean, https://github.com/google-deepmind/formal-conjectures; Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009, Chapter 2.6

import Definitions.Def_PvsNP_complexity_classes

namespace PvsNP

theorem NP_ne_coNP : NP ≠ coNP := by sorry

end PvsNP
