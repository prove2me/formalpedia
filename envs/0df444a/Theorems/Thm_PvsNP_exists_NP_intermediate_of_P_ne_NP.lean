-- Prove2me | Theorems.Thm_PvsNP_exists_NP_intermediate_of_P_ne_NP
-- name    : PvsNP.exists_NP_intermediate_of_P_ne_NP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T04:17:52.288291+00:00
-- url     : https://prove2.me/theorems/b07a15ed-a0f1-40ed-92c3-e4fd07328278
-- title:
--   Ladner's theorem: $\mathsf{NP}$-intermediate problems exist if $\mathsf{P} \ne \mathsf{NP}$
-- statement:
--   Assume $\mathsf{P} \ne \mathsf{NP}$. Then there is a decision problem in $\mathsf{NP}$ that is neither in $\mathsf{P}$ nor $\mathsf{NP}$-hard, i.e. an $\mathsf{NP}$-intermediate problem. This is Ladner's theorem (1975), proved by delayed diagonalisation.
-- source:
--   Richard E. Ladner, On the structure of polynomial time reducibility, J. ACM 22(1), 1975, pp. 155-171, https://doi.org/10.1145/321864.321877

import Definitions.Def_PvsNP_reductions

namespace PvsNP

theorem exists_NP_intermediate_of_P_ne_NP (h : P ≠ NP) :
    ∃ L : DecisionProblem, L ∈ NP ∧ L ∉ P ∧ ¬ NPHard L := by sorry

end PvsNP
