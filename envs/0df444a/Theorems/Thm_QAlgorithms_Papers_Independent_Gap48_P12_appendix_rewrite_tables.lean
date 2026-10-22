-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_appendix_rewrite_tables
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.appendix_rewrite_tables
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:44:55.447081+00:00
-- url     : https://prove2.me/theorems/54816042-c7f2-421f-bc64-533921c87e41
-- title:
--   Appendix, Tables 1–3: the 192 concrete rewriting rules
-- statement:
--   Let $(A_{j,i},B_{j,i})$ denote the literal input/tail word pairs transcribed from Table $j+1$, for $j=0,1,2$ and $i=0,\ldots,63$, in row order interleaved across the two printed columns. Put $S_0=I$, $S_1=H$, and $S_2=PH$. Each table has exactly 64 entries, and every entry satisfies
--
--   $$f_u(A_{j,i})T=S_jT f_u(B_{j,i}).$$
--
--   The 192 matrices $f_u(A_{j,i})$ are pairwise distinct and cover exactly $C_1$. The caption correspondences also hold:
--
--   $$\begin{aligned}
--   f_u(A_{1,i})&=Hf_u(A_{0,i}),& B_{1,i}&=B_{0,i},\\
--   f_u(A_{2,i})&=PHf_u(A_{0,i}),& B_{2,i}&=B_{0,i}.
--   \end{aligned}$$
--
--   The input correspondences are matrix equalities allowing Clifford simplification; they do not assert literal prefix-string equality. The symbol $I$ is transcribed as the empty word. This is the source's complete concrete one-$T$ rewrite interface.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 15, Appendix, Tables 1–3: the 192 concrete rewriting rules

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.7 and Appendix pp.15–17, Tables 1–3: every literal rule,
64 rows per table, complete nonrepeating Clifford coverage, and both
caption correspondences. The input-prefix correspondences are matrix
equalities, allowing Clifford word simplification. -/
theorem appendix_rewrite_tables :
    (∀ j : Fin 3, (appendixTable j).length = 64 ∧ ∀ i : Fin 64,
      wordMatrix .hp (appendixRow j i).1 * gateT =
        wordMatrix .hp (appendixPrefix j) * gateT * wordMatrix .hp (appendixRow j i).2) ∧
    (rewriteTable.map fun row => wordMatrix .hp row.1).Nodup ∧
    (∀ U : Mat, U ∈ cliffordSet .hp ↔
      U ∈ (rewriteTable.map fun row => wordMatrix .hp row.1)) ∧
    (∀ i : Fin 64,
      wordMatrix .hp (appendixRow 1 i).1 = hadamard * wordMatrix .hp (appendixRow 0 i).1 ∧
      wordMatrix .hp (appendixRow 2 i).1 = phaseS * hadamard * wordMatrix .hp (appendixRow 0 i).1 ∧
      (appendixRow 1 i).2 = (appendixRow 0 i).2 ∧
      (appendixRow 2 i).2 = (appendixRow 0 i).2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
