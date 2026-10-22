-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_local_unitary_invariance
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.local_unitary_invariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:25:38.516678+00:00
-- url     : https://prove2.me/theorems/9e62c868-b2a5-43e0-8984-2f8cdb8f50a3
-- title:
--   Local unitary invariance
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   For every bipartite state $\rho_{AB}$ and unitaries $U_A$ and $U_B$ on the respective local spaces,
--
--   $$E_I\bigl((U_A\otimes U_B)\rho(U_A\otimes U_B)^\dagger\bigr)=E_I(\rho).$$
--
--   This records invariance under local changes of orthonormal basis. The formal predicate compares normalized states on the same local spaces through this actual conjugation.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 2, Unnumbered: local unitary invariance

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, axiom 1: local unitary transformations leave CEMI invariant. -/
theorem local_unitary_invariance :
    IsLocalUnitaryInvariant (cemiFunctional (n := 2)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
