-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_authorizedCapacitySaturation
-- name    : QAlgorithms.Papers.Independent.Information100.P22.authorizedCapacitySaturation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:05:43.944424+00:00
-- url     : https://prove2.me/theorems/6d937400-ab88-4015-ab79-24911ae55cfa
-- title:
--   Eq.(2), unnumbered: authorized-channel capacity saturation
-- statement:
--   For $m,k\ge1$, a normalized pure resource and an AS unitary that leaves the common key untouched, suppose a fixed CPTP decoder exactly reverses the authorized channel $Q_i$. Then
--   $$I(\widetilde A\rangle S_iN)_\Omega=Q^{(1)}(Q_i)=C_Q(Q_i)=k.$$
--   Here the first quantity is coherent information at the maximally mixed input, $Q^{(1)}$ optimizes over every density input, and $C_Q$ is unassisted quantum capacity, represented by regularized optimized coherent information over positive block lengths. This is capacity saturation, stronger than mere existence of a decoder.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 3, Eq.(2), unnumbered: authorized-channel capacity saturation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eq.(2), PDF p.3; explanation pp.8,19,23. No inference of strict capacity loss from a failed certificate. -/
theorem authorizedCapacitySaturation (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R)
    (U : Matrix.unitaryGroup (Qubits k × Signals m k) ℂ) (i : Fin m)
    (hrec : Recoverable R (U : Op _) i) :
    coherentInformation (authorized R (U : Op _) i) (mixed (Qubits k)) = k ∧
    singleUseInformation (authorized R (U : Op _) i) = k ∧
    quantumCapacity (authorized R (U : Op _) i) = k := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
