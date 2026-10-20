-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_lemmaB12
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.lemmaB12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:21:13.561895+00:00
-- url     : https://prove2.me/theorems/6e727464-b0ef-4e15-baed-cf92abf48c00
-- title:
--   Classical and assisted scrambling times of classical channels coincide
-- statement:
--   Let $A\in M_d(\mathbb C)$, $d\ge1$, have real nonnegative entries and column sums one. Define the classical channel $\Phi_A(X)=\operatorname{diag}(A\operatorname{diag}X)$. If $c,c_E$ are the first positive times at which its one-shot zero-error classical and assisted capacities vanish, with infinity when no such time exists, then
--
--   $$c(\Phi_A)=c_E(\Phi_A).$$
--
--   This compares the times of capacity extinction, including nonmixing channels with infinite indices; it does not identify positive assisted and unassisted capacities.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 21, Lemma B.12

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

/-- Lemma B.12, PDF p.21: equality of the two indices, including infinity,
not equality of their possibly positive capacities. -/
theorem lemmaB12 {d : ℕ} (hd : 0 < d) (A : Operator d) (hA : ColumnStochastic A) :
    classicalTime (Information100.P62.classicalChannel (A.map Complex.re)) = assistedTime (Information100.P62.classicalChannel (A.map Complex.re)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
