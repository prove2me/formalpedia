-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_threeSteps_suffice
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.threeSteps_suffice
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:08:08.252792+00:00
-- url     : https://prove2.me/theorems/ce9fc634-ad95-4665-8ade-b3e8e3268562
-- title:
--   Three finite interaction intervals suffice for a pure interaction
-- statement:
--   Let $H$ be a Hermitian Hamiltonian on two qubits $A,B$, with canonical interaction coefficients $\alpha=(\alpha_1,\alpha_2,\alpha_3)$ satisfying $\alpha_1\ge\alpha_2\ge|\alpha_3|$. Local terms in $H$ are allowed. Local unitary controls are instantaneous and free, interaction intervals are nonnegative, and $\hbar=1$. Write $C_H(U)$ for the infimum of the interaction durations of protocols implementing the gate $U$, allowing the ideal limit of arbitrarily fine pulses at fixed total duration and disregarding global phase. This cost is an extended nonnegative real, with value $+\infty$ for an impossible simulation. Assume $\alpha_1>0$ and $H=\sum_{i,j=1}^3 c_{ij}\sigma_i\otimes\sigma_j$ with real $c_{ij}$ and Pauli matrices $\sigma_1=X,\sigma_2=Y,\sigma_3=Z$, so there are no local or scalar terms. For every two-qubit gate $U$ there is a finite protocol with local controls and nonnegative intervals $t_1,\ldots,t_m$ such that
--
--   $$m\le3,\qquad U_{\rm protocol}=e^{i\theta}U,\qquad \sum_{j=1}^{m}t_j=C_H(U).$$
--
--   Here $\theta$ is a real global phase. Zero intervals and local target gates are allowed. For a pure interaction, an optimal protocol needs no infinitesimal simulation.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 6, III.C: three finite interaction steps for a pure interaction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.6, III.C: for a pure interaction every gate has an optimal finite exact
protocol with at most three nonnegative interaction intervals (zero durations allowed). -/
theorem threeSteps_suffice (H U : TwoMatrix) (a : Triple)
    (hH : HasCanonicalHamiltonian H a) (hPure : PureInteraction H)
    (ha : 0 < a 0) (hU : IsGate U) :
    ∃ p : PulseProtocol, p.pulses.length ≤ 3 ∧
      SamePhysicalGate (protocolMatrix H p) U ∧
      (protocolTime p : ℝ≥0∞) = interactionCost H U := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
