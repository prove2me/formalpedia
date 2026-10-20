-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_pureResourceInvariance
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.pureResourceInvariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:04:10.712579+00:00
-- url     : https://prove2.me/theorems/66a5d595-3215-4762-b741-e599528ada3b
-- title:
--   §II.A: independence from the pure entanglement resource
-- statement:
--   Let $\mathcal N$ be a memoryless CPTP map between nonzero finite-dimensional complex Hilbert spaces. Fix a normalized pure bipartite state $|\psi\rangle$ on finite nonzero spaces $J\otimes I$, with Alice holding $I$ and Bob holding $J$, whose entanglement entropy satisfies $H(\operatorname{Tr}_J|\psi\rangle\langle\psi|)>0$. Let $C_\psi(\mathcal N)$ be the operational classical capacity when an unlimited number of copies of this fixed state is available before the message. Encoding is arbitrary local CPTP processing, decoding is collective, and the only communication is through the forward channel. Error vanishes uniformly over messages. Then
--
--   $$C_\psi(\mathcal N)=C_E(\mathcal N).$$
--
--   Here $C_E$ uses standard EPR pairs and all rates and entropies are in bits. This is an equality of capacities with unlimited resources, not an equality of finite entanglement costs.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 13, §II.A: independence from the pure entanglement resource

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF p.13, §II.A: unlimited normalized pure entangled resources give equal capacities. -/
theorem pureResourceInvariance {I J A B : Type*} [Fintype I] [Fintype J]
    [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
    [DecidableEq A] [DecidableEq B] [Nonempty I] [Nonempty J] [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (psi : EuclideanSpace ℂ (J × I))
    (hpsi : ‖psi‖ = 1) (hent : 0 < vnEntropy (traceLeft (pureDensity psi))) :
    resourceCapacity psi N = resourceCapacity standardEbit N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
