-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_redistributionOuterBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.redistributionOuterBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:15:00.660369+00:00
-- url     : https://prove2.me/theorems/75d72515-64ad-42ce-8838-4a44aecde08d
-- title:
--   Proposition 5.1: redistribution converse outer bound
-- statement:
--   Let $|\psi\rangle^{R\widehat A\widehat B B}$ be a normalized pure state on finite nonzero registers. Alice initially owns $\widehat A\widehat B$, Bob owns $B$, and $R$ is inaccessible. A redistribution protocol transfers $\widehat B$ to Bob, leaves $\widehat A$ with Alice, and reconstructs the joint source/reference state and final Bell pairs with vanishing full trace-norm error. Only one-way qubit communication, Bell resources, and arbitrary local CPTP maps are allowed.
--
--   Every asymptotically achievable pair of qubit rate $Q$ and signed net Bell consumption rate $E$ satisfies
--   $$Q\ge\tfrac12 I(\widehat B;R\mid\widehat A)_\psi,\qquad Q+E\ge H(\widehat B\mid B)_\psi.$$
--   Rates use every positive error and rate slack and all sufficiently large positive IID blocklengths. All information quantities are in bits and are computed from this same pure source.
--
--   This is a converse outer bound. The conditional mutual information is stated with the printed conditioning register $\widehat A$; pure-state entropy duality identifies it with conditioning on $B$.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 18, Proposition 5.1: redistribution converse outer bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.18, Proposition 5.1: converse only, with the source's conditioning
on Ahat and signed net Bell consumption. Alice retains Ahat and Bob retains B. -/
theorem redistributionOuterBound {A C B R : Type}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty C] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (hpsi : IsState psi)
    (Q E : ℝ) (h : RedistributionAchievable psi Q E) :
    printedQuantumCost psi ≤ Q ∧ conditionalCost psi ≤ Q + E := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
