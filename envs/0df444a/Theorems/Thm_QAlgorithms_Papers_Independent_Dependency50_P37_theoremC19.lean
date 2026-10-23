-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremC19
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremC19
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:30:37.912645+00:00
-- url     : https://prove2.me/theorems/8190fcb0-cacc-411f-ae35-483ce3ccb6c8
-- title:
--   Primitivity of a stochastic matrix is eventual strict positivity
-- statement:
--   Let $A\in M_d(\mathbb C)$, $d\ge1$, be real nonnegative and column stochastic. It is primitive when it is mixing and its invariant probability vector has full support. Strict positivity means that every matrix entry is positive. Then
--
--   $$A\text{ is primitive}\iff\exists k\ge1:\ A^k\text{ is strictly positive}.$$
--
--   This is the local classical specialization of the explicitly credited C.5.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 29, Theorem C.19

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

/-- Theorem C.19, PDF p.29: classical specialization of the credited C.5. -/
theorem theoremC19 {d : ℕ} (hd : 0 < d) (A : Operator d) (hA : ColumnStochastic A) :
    MatrixPrimitive A ↔ ∃ k : ℕ, 0 < k ∧ MatrixStrictlyPositive (A ^ k) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
