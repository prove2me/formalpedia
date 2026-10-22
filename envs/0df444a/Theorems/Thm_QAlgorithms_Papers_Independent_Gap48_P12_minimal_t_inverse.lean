-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_minimal_t_inverse
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.minimal_t_inverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:39:14.407991+00:00
-- url     : https://prove2.me/theorems/53dc38c5-7694-4b01-ac49-b7f5c2522041
-- title:
--   Lemma 1: inverse closure of the exact minimal-T layers
-- statement:
--   Let $M_n$ be the exact matrices admitting words with at most $n$ literal $T$ gates. Define $M_{=0}=M_0$ and $M_{=n}=M_n\setminus M_{n-1}$ for $n\ge1$. Fix the shortest Clifford representatives. If $C$ is normal, contains exactly $n$ $T$ letters, and $f_u(C)\in M_{=n}$, then
--
--   $$f_u(C)^{-1}=f_u(C)^\dagger\in M_{=n}.$$
--
--   The integer $n$ is nonnegative. The definition at zero preserves the case explicitly treated in the source proof. This asserts inverse closure of minimal-cost layers, rather than closure of mere syntactic counts.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 8, Lemma 1: inverse closure of the exact minimal-T layers

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.8, Lemma 1: preserve both the normal-word and minimal-layer
premises. Inversion of the evaluated unitary is its adjoint.
The zero layer is M₀, as required by the source proof's n=0 case. -/
theorem minimal_t_inverse (reps : Representatives .hp) (n : ℕ)
    (C : CircuitWord) (hC : IsNormalWord .hp reps C) (ht : wordTCount C = n)
    (hminimal : wordMatrix .hp C ∈ minimalT n) :
    star (wordMatrix .hp C) ∈ minimalT n := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
