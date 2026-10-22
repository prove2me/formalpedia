-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_one_t_clifford_rewrite
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.one_t_clifford_rewrite
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:36:33.777601+00:00
-- url     : https://prove2.me/theorems/1da56676-cb52-420f-8d60-ed4ecf64dfea
-- title:
--   Section 4.1, unnumbered: complete one-T Clifford rewrite
-- statement:
--   Fix the selected shortest Clifford representatives $r(U)$ for $U\in C_1$. For every exact Clifford matrix $W\in C_1$, there are $S\in\{I,H,PH\}$ and $U\in C_1$ satisfying
--
--   $$WT=ST f_u(r(U)).$$
--
--   Here $f_u(r(U))=U$, with global phase retained. This is the complete local one-$T$ rewrite, including its representation by the fixed Clifford tail.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 7, Section 4.1, unnumbered: complete one-T Clifford rewrite

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.7, §4.1 after Fact 1: complete one-T Clifford rewrite,
with W₁ represented by the fixed selected shortest word. -/
theorem one_t_clifford_rewrite (reps : Representatives .hp)
    (W : Mat) (hW : W ∈ cliffordSet .hp) :
    ∃ S : Mat, S ∈ ({1, hadamard, phaseS * hadamard} : Set Mat) ∧
      ∃ U : Mat, U ∈ cliffordSet .hp ∧
        W * gateT = S * gateT * wordMatrix .hp (reps.word U) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
