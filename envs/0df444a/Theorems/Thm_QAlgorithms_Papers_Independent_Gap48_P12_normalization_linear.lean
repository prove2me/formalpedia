-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_normalization_linear
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.normalization_linear
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:37:20.681875+00:00
-- url     : https://prove2.me/theorems/467a3aff-9166-4a6b-87f7-67caaf3d5844
-- title:
--   Section 4.1: linear-time normalization
-- statement:
--   Fix the shortest Clifford representative system $r$. Let $N_r(C)$ be the explicitly defined left-to-right table/stack normalization of the input word $C$: Clifford letters update the current tail; a $T$ uses the appendix rewrite table; an internal identity prefix merges adjacent $TT$ into $P$ and pops the preceding block. Let $t(C)$ count its actual $T$ letters, and let $\tau_r(C)$ be the attached operation count, charging input reads, fixed finite-table operations, stack edits, and output materialization. Then there is a constant $K>0$, chosen before every input word, such that
--
--   $$\forall C:\quad N_r(C)\in\mathcal N_r,\quad f_u(N_r(C))=f_u(C),\quad t(N_r(C))\le t(C),\quad \tau_r(C)\le K(|C|+1).$$
--
--   The bound covers the empty word. Fixed Clifford products and representative selections are finite table primitives because the alphabet and exact Clifford group are fixed. The implementation is given by local definition bodies; normalization correctness is a conclusion, not a field of an assumed algorithm. No simultaneous $H/T$ optimality claim is made.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 8, Section 4.1: linear-time normalization

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF pp.7–8, §4.1: the defined table/stack normalizer returns an
exactly equivalent normal word, never increases its T-count, and runs in
linear time in the fixed finite-table unit-cost model, including materialization.
The affine bound covers the empty word. Constants precede every input word.
No simultaneous H/T optimality is asserted. -/
theorem normalization_linear (reps : Representatives .hp) :
    ∃ K : ℕ, 0 < K ∧ ∀ C : CircuitWord,
      IsNormalWord .hp reps (normalizeWord reps C) ∧
      wordMatrix .hp (normalizeWord reps C) = wordMatrix .hp C ∧
      wordTCount (normalizeWord reps C) ≤ wordTCount C ∧
      normalizationCost reps C ≤ K * (C.length + 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
