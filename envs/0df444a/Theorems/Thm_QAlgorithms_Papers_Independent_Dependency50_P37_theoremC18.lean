-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremC18
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremC18
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:29:54.399987+00:00
-- url     : https://prove2.me/theorems/f7f7725c-6934-461e-b7bc-731ebb64adb3
-- title:
--   Mixing stochastic matrices have an eventually scrambling power
-- statement:
--   Let $A\in M_d(\mathbb C)$, $d\ge1$, be real nonnegative and column stochastic. Mixing means $A^nx\to(\sum_jx_j)v$ for every vector $x$, for one invariant probability vector $v$; equivalently, eigenvalue $1$ is simple and there are no other modulus-one eigenvalues. A matrix is scrambling when every pair of columns has overlapping support. Then
--
--   $$A\text{ is mixing}\iff\exists k\ge1:\ A^k\text{ is scrambling}.$$
--
--   This is the paper's local classical specialization of B.1.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 29, Theorem C.18

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

/-- Theorem C.18, PDF p.29: local classical specialization of B.1. -/
theorem theoremC18 {d : ℕ} (hd : 0 < d) (A : Operator d) (hA : ColumnStochastic A) :
    MatrixMixing A ↔ ∃ k : ℕ, 0 < k ∧ MatrixScrambling (A ^ k) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
