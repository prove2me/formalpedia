-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P39_entangledPureCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P39.entangledPureCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:00:59.861519+00:00
-- url     : https://prove2.me/theorems/ccad25a7-6b02-426c-a587-a635aa443d42
-- title:
--   Every entangled pure state supplies capacity two
-- statement:
--   Let $\rho_{AB}$ be a positive semidefinite density operator of trace one on two nonzero finite dimensional complex registers $A$ and $B$, whose dimensions may differ. Alice and Bob receive arbitrarily many independent copies of this one fixed state for free. Alice may send quantum systems to Bob through a noiseless channel; there is no free classical communication or feedback. Arbitrary local CPTP encodings, ancillas, disposal, and joint decoding are allowed. Entropies use logarithms to base two.
--
--   Write $C_{\rm sd}(\rho)$ for the operational supremum of classical bits per transmitted qubit: first choose integers $d\ge2$ and $n\ge1$; a block of $k$ channel uses sends a system of dimension $d^k$ and consumes $nk$ copies. For each error tolerance and rate slack, all sufficiently large positive $k$ admit encoders for all $m$-bit messages and one common decoder whose success is at least $1-\epsilon$ for every message. The normalized rate is $m/(k\log_2d)$, with vanishing error and arbitrarily small rate slack.
--
--   Let $\psi\in A\otimes B$ have norm one, and assume $|\psi\rangle\langle\psi|$ is entangled. Then
--
--   $$
--   C_{\rm sd}(|\psi\rangle\langle\psi|)=2.
--   $$
--
--   This includes nonmaximal Schmidt spectra and unequal local dimensions. Unlimited copies and compression allow the optimal two-bit rate even when the entanglement entropy of one copy is arbitrarily small but positive. Product pure states are excluded.
-- source:
--   Classical capacity of a noiseless quantum channel assisted by noisy entanglement, arXiv:quant-ph/0106080v3, PDF p. 8, Section 2, consequence after Eq. (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

namespace QAlgorithms.Papers.Independent.Support50.P39

noncomputable section

open QAlgorithms

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:quant-ph/0106080v3, PDF p.8: every normalized entangled pure
resource has capacity two bits per transmitted qubit with unlimited copies,
including nonmaximal Schmidt spectra and unequal local dimensions.
Product pure states are excluded by inseparability, not by a maximality condition. -/
theorem entangledPureCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1)
    (hent : ¬ QAlgorithms.Entanglement.IsSeparableDensity (pureDensity psi)) :
    denseCodingCapacity (pureDensity psi) = 2 := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P39
