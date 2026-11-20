-- Prove2me | Theorems.Thm_TetrisHard_Rows_threePartition_mem_NP
-- name    : TetrisHard.Rows.threePartition_mem_NP
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:26:09.430039+00:00
-- url     : https://prove2.me/theorems/42a8b149-0bee-4620-9e26-d14f7e39dbf4
-- title:
--   Unary 3-Partition lies in NP
-- statement:
--   Let $\mathrm{3\text{-}Partition}$ denote the language of self-delimiting unary encodings $\langle s, T, a_1, \dots, a_{3s}\rangle \in \{0,1\}^*$ of valid 3-Partition instances $(s, T, a_1, \dots, a_{3s})$ (satisfying $\sum_{i=1}^{3s} a_i = sT$ and $T/4 < a_i < T/2$ for all $i$) that admit a partition into $s$ triples each summing to $T$. Then
--   $$\mathrm{3\text{-}Partition} \in \mathrm{NP}.$$
--
--   A nondeterministic certificate specifies the part index $j_i \in \{0, \dots, s-1\}$ assigned to each $a_i$ in unary; its length is bounded quadratically in the unary input length, and validity plus the $s$ part-sum equations are verifiable in polynomial time on a one-tape Turing machine.
-- source:
--   Garey and Johnson, Computers and Intractability: A Guide to the Theory of NP-Completeness (1979), Theorem 4.4 (pp. 96-105); Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 3 (p. 7)

import Definitions.Def_TetrisHard_Rows_ThreePartition

namespace TetrisHard.Rows

theorem threePartition_mem_NP :
    threePartitionLanguage ∈ CookPvsNP.NP Bool := by sorry

end TetrisHard.Rows
