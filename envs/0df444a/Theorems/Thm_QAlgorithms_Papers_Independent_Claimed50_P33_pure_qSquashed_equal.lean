-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_pure_qSquashed_equal
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.pure_qSquashed_equal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:47:29.766791+00:00
-- url     : https://prove2.me/theorems/1ed9a9d5-6edf-4299-acd2-00fff4dbdf59
-- title:
--   §IV.G remark: the two q versions agree on pure states
-- statement:
--   Let $m\ge2$ and let $|\psi\rangle$ be a unit vector in the tensor product of finite nonzero local Hilbert spaces. For the unrestricted squashed measures without $1/2$,
--
--   $$E_{I_m}^q(|\psi\rangle\langle\psi|)=E_{S_m}^q(|\psi\rangle\langle\psi|).$$
--
--   This identifies the two quantum versions on pure states, leaving their equality on general mixed states open as in the source.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 8, §IV.G remark: the two q versions agree on pure states

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section IV.G, PDF p.8: the two q versions agree on normalized pure
states. Equality on arbitrary mixed states is left open by the source. -/
theorem pure_qSquashed_equal {m : ℕ} (hm : 2 ≤ m)
    {D : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (psi : EuclideanSpace ℂ (RegisterBasis D)) (hpsi : ‖psi‖ = 1) :
    multipartiteSquashed false .total (pureDensity psi) =
      multipartiteSquashed false .dual (pureDensity psi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
