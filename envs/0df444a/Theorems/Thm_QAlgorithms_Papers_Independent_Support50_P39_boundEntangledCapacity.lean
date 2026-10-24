-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P39_boundEntangledCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P39.boundEntangledCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:58:26.731823+00:00
-- url     : https://prove2.me/theorems/304a25fc-f38e-4d80-9c79-57ac64f8ee77
-- title:
--   Bound entangled states give exactly the unassisted capacity
-- statement:
--   Let $\rho_{AB}$ be a positive semidefinite density operator of trace one on two nonzero finite dimensional complex registers $A$ and $B$, whose dimensions may differ. Alice and Bob receive arbitrarily many independent copies of this one fixed state for free. Alice may send quantum systems to Bob through a noiseless channel; there is no free classical communication or feedback. Arbitrary local CPTP encodings, ancillas, disposal, and joint decoding are allowed. Entropies use logarithms to base two.
--
--   Write $C_{\rm sd}(\rho)$ for the operational supremum of classical bits per transmitted qubit: first choose integers $d\ge2$ and $n\ge1$; a block of $k$ channel uses sends a system of dimension $d^k$ and consumes $nk$ copies. For each error tolerance and rate slack, all sufficiently large positive $k$ admit encoders for all $m$-bit messages and one common decoder whose success is at least $1-\epsilon$ for every message. The normalized rate is $m/(k\log_2d)$, with vanishing error and arbitrarily small rate slack.
--
--   Suppose $\rho$ is bound entangled: it is inseparable and cannot be distilled to singlets by local quantum operations and two-way classical communication. Then
--
--   $$
--   C_{\rm sd}(\rho)=1.
--   $$
--
--   Thus bound entanglement gives no dense-coding advantage. Distillation here defines the resource class; it does not add free classical communication to the dense-coding protocol.
--
--   **Formalization Note** The exact finite-copy two-qubit local-filter characterization of distillability is used, as established in the paper's Ref. 11. This includes every nondistillable entangled state, rather than only PPT states. Local images need remain nondistillable, but may become separable.
-- source:
--   Classical capacity of a noiseless quantum channel assisted by noisy entanglement, arXiv:quant-ph/0106080v3, PDF p. 3, Section 1, consequence after Eq. (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

namespace QAlgorithms.Papers.Independent.Support50.P39

noncomputable section

open QAlgorithms

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:quant-ph/0106080v3, PDF pp.1,3: ALL bound entangled states have
capacity exactly one, including the unassisted baseline. Distillability is
unrestricted LOCC distillability, characterized by the source's cited Ref. 11.
A local image need only remain nondistillable; the source's claim that every
image remains entangled is not used (discarding can yield a separable state). -/
theorem boundEntangledCapacity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hbound : IsBoundEntangled rho) :
    denseCodingCapacity rho = 1 := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P39
