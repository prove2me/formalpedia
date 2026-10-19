-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_decouplingCriterion
-- name    : QAlgorithms.Papers.Independent.Information100.P32.decouplingCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:42:50.380367+00:00
-- url     : https://prove2.me/theorems/46b35ebc-0cf7-4c3c-9b8b-92e7469a9710
-- title:
--   Sector invariance is equivalent to dephasing covariance
-- statement:
--   Work in arbitrary finite nonempty system and ancillary Hilbert spaces with fixed orthonormal reference bases. Write $\mathcal D(X)_{ij}=\delta_{ij}X_{ii}$ for complete dephasing in the specified basis. A density matrix is positive semidefinite with trace one; a channel is completely positive and trace preserving. Population–coherence decoupling means that diagonal and zero-diagonal operator sectors are each invariant, on all operators. For every channel $\Phi$,
--   $$\Phi\text{ preserves both sectors}\quad\Longleftrightarrow\quad
--   \mathcal D\Phi(X)=\Phi\mathcal D(X)\text{ for every operator }X.$$
--   This criterion concerns the reduced channel, and includes both directions on all operators.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 15, Appendix A Eqs.(A1)–(A8): exact decoupling criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.15, Eqs.(A1)–(A8): both sector invariances are equivalent to commuting
with dephasing, on every operator in arbitrary finite nonempty dimension. -/
theorem decouplingCriterion {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (f : Op I → Op I) (hf : IsChannel f) :
    Decoupled f ↔ ∀ x : Op I, diagonal (f x) = f (diagonal x) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
