-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_degenerateRedistributionTightness
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.degenerateRedistributionTightness
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:15:53.307018+00:00
-- url     : https://prove2.me/theorems/e9540193-0085-42a4-a1f3-433b1b1b644b
-- title:
--   Unnumbered result: tightness for absent sender/receiver side information
-- statement:
--   Let $|\psi\rangle^{R\widehat A\widehat B B}$ be a normalized pure state on finite nonzero registers, with initial ownership $\widehat A\widehat B$ at Alice and $B$ at Bob. Suppose $\dim\widehat A=1$ or $\dim B=1$. Null registers have dimension one.
--
--   For the same one-way qubit and signed Bell-resource redistribution task, a pair $(Q,E)$ is achievable if and only if
--   $$Q\ge\tfrac12 I(\widehat B;R\mid\widehat A)_\psi,\qquad Q+E\ge H(\widehat B\mid B)_\psi.$$
--   Achievability uses arbitrary local CPTP maps, separate Bell input/output counts, every positive error and rate slack, all sufficiently large positive IID blocks, and full joint source/reference and final Bell-pair trace-norm error. All entropies are in bits.
--
--   For absent sender side information the FQSW corner achieves the outer bound; for absent receiver side information the FQRS corner does so. Allowed resource trades extend the corner to the whole displayed region.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 18, Unnumbered result: tightness for absent sender/receiver side information

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.18: the outer region is achieved if Ahat or B is null. Null means
one-dimensional, never empty; arbitrary extra qubits can be traded for Bell pairs. -/
theorem degenerateRedistributionTightness {A C B R : Type}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty C] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (hpsi : IsState psi)
    (hnull : Fintype.card A = 1 ∨ Fintype.card B = 1) (Q E : ℝ) :
    RedistributionAchievable psi Q E ↔
      printedQuantumCost psi ≤ Q ∧ conditionalCost psi ≤ Q + E := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
