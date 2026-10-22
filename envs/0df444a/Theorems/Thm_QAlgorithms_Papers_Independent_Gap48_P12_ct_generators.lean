-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_ct_generators
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.ct_generators
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:34:57.90595+00:00
-- url     : https://prove2.me/theorems/1d590058-9a03-4525-8119-1b615dee3a8b
-- title:
--   Section 4.1, unnumbered: generators of C_T(C_1)
-- statement:
--   For the exact Clifford group $C_1=\langle H,P\rangle$ and the image-defined subgroup $C_T(C_1)$ on page 7,
--
--   $$C_T(C_1)=\langle P,\ HP^2H,\ (HP^3)^3\rangle.$$
--
--   These are exact matrix groups. The symbolic third generator evaluates to $e^{-i\pi/4}I$; the following printed display $e^{i\pi/8}I$ is erroneous. Keeping the symbolic word preserves the asserted group and its global phases. The result identifies the generators used by the local rewrite construction.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 7, Section 4.1, unnumbered: generators of C_T(C_1)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.7, §4.1: the printed symbolic generator assertion.
Source discrepancy: the following “namely” display prints exp(i*pi/8) I;
the word (H P^3)^3 actually equals exp(-i*pi/4) I. We retain the symbolic
word and exact phases; independent moderation of the correction is required. -/
theorem ct_generators :
    (generatedCT : Set (Matrix.unitaryGroup Bool ℂ)) = {u : Matrix.unitaryGroup Bool ℂ | (u : Mat) ∈ ctSet} := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
