-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_degradableQuantumCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.degradableQuantumCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:10:42.963695+00:00
-- url     : https://prove2.me/theorems/02604758-fd74-478a-aebe-14d21f1a9f62
-- title:
--   Appendix B (18): degradable operational quantum capacity
-- statement:
--   Let $A',B,E$ be finite nonzero complex registers and let $U:A'\to B\otimes E$ be an isometry. Define $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its complementary channel $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Suppose a CPTP degrading map $T:B\to E$ satisfies $\mathcal N^c=T\circ\mathcal N$ on all operators. Let $Q(\mathcal N)$ be the unassisted operational quantum capacity, defined by asymptotic CPTP entanglement-transmission encoders and decoders on all full tensor powers. Then
--
--   $$
--   Q(\mathcal N)=\max_{\rho\geq0,\ \operatorname{Tr}\rho=1}
--   \bigl[H(\mathcal N(\rho))-H(\mathcal N^c(\rho))\bigr].
--   $$
--
--   The maximum is attained by an input density matrix; its value bounds the coherent information of every other input density matrix. Entropies are in bits. No product-input restriction is imposed in the operational capacity.
--
--   This removes regularization for the quantum axis of a finite-dimensional degradable channel. It supplies no infinite-dimensional normal-channel or infinite-capacity assertion.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 13, Appendix B (18): degradable operational quantum capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Appendix B, PDF p.13, (18): OPERATIONAL quantum capacity equals the attained
one-letter maximum for a finite-dimensional degradable channel. The degrader is
CPTP, the complement uses the same isometry, and no product-input restriction is
introduced. This does not assert an infinite-dimensional normal-channel theorem. -/
theorem degradableQuantumCapacity
    [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U) :
    quantumCapacity (receiverChannel U) = maximumCoherentInformation U ∧
    ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
      quantumCapacity (receiverChannel U) =
        vnEntropy (receiverChannel U rho) - vnEntropy (complementaryChannel U rho) ∧
      ∀ sigma : Matrix A A ℂ, IsDensityMatrix sigma →
        vnEntropy (receiverChannel U sigma) - vnEntropy (complementaryChannel U sigma) ≤
          vnEntropy (receiverChannel U rho) - vnEntropy (complementaryChannel U rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
