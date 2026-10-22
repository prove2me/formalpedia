-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_markov_unitary_invariance
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.markov_unitary_invariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:42:24.002474+00:00
-- url     : https://prove2.me/theorems/0fc86fda-688d-4528-9135-1ae9ac9b2bc6
-- title:
--   Invariance under local one-particle unitaries
-- statement:
--   Let $H=H_1\oplus H_2\oplus H_3$ be a finite-dimensional complex Hilbert space and let $A\ge0$ be the one-particle covariance of its quasifree state. Write $\mathcal S(T)=\operatorname{Tr}g(T)$, where $g(x)=(x+1)\log(x+1)-x\log x$ with $0\log0=0$. The Markov condition is the actual quasifree marginal entropy identity
--
--   $$\mathcal S(A)-\mathcal S(A_{23,23})=\mathcal S(A_{12,12})-\mathcal S(A_{22}).$$
--
--   If $A$ satisfies it and $U=\operatorname{diag}(U_1,U_2,U_3)$ with each $U_i$ unitary on $H_i$, then $U^*AU$ satisfies the same Markov condition. This preserves Markovness under changes of orthonormal coordinates within each time block, including vacuum modes.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 14, Corollary 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

/-- Corollary 2.1, PDF p.14: block-unitary invariance of the entropy Markov condition;
no faithfulness assumption or imaginary power at zero is used. -/
theorem markov_unitary_invariance (A : Mat (I ⊕ (J ⊕ K))) (hA : A.PosSemidef)
    (U1 : Matrix.unitaryGroup I ℂ) (U2 : Matrix.unitaryGroup J ℂ)
    (U3 : Matrix.unitaryGroup K ℂ) (hMarkov : IsMarkov A) :
    let U := diagonal3 (U1 : Mat I) (U2 : Mat J) (U3 : Mat K)
    IsMarkov (U.conjTranspose * A * U) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
