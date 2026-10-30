-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_fact39
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.fact39
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:01:39.071209+00:00
-- url     : https://prove2.me/theorems/2a8dd890-93b2-4796-8696-01b2fba539c6
-- title:
--   Fact 39: maximally entangled contraction of physical projectors
-- statement:
--   Let $N\ge1,d\ge1$, let $\alpha\vdash N-1$, $\mu\vdash N$ be physical compatible shapes, and use the concrete Eq. (145) operator $F_\mu(\alpha)$. Let $P_\alpha$ be the actual central tensor-permutation projector and $m_\lambda$ the actual tensor multiplicities. Define $J u=u\otimes|\Phi^+\rangle$ on the first $N-1$ and final two factors, with the Bell vector normalized. For $u,v$ in the image of $P_\alpha$,
--
--   $$\langle Ju,F_\mu(\alpha)Jv\rangle=\frac{m_\mu}{d\,m_\alpha}\langle u,v\rangle.$$
--
--   On any orthonormal basis of the actual alpha-isotypic copies this is exactly Eq. (136), with the two Kronecker deltas. The inner product is conjugate-linear in its first argument; arbitrary unrelated basis certificates are not used.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 29, Fact 39: maximally entangled contraction of physical projectors

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Fact 39, Eq.(136), in the equivalent sesquilinear form on the actual alpha
isotypic subspace (PDF p.29). F is constructed by Eq.(145); u,v are in the image
of the actual central projector. On its orthonormal copy basis this is exactly
(m_mu/(d m_alpha)) delta_kl delta_rs. -/
theorem fact39 {d K : ℕ} (hd : 0 < d) (alpha : Partition d K) (mu : Partition d (K+1))
    (hedge : Predecessor alpha.val mu.val)
    (u v : AliceIndex d K → ℂ)
    (hu : isotypicProjector alpha *ᵥ u = u) (hv : isotypicProjector alpha *ᵥ v = v) :
    dotProduct (star u)
      (((pbtBellEmbedding d K)ᴴ * physicalProjector alpha mu * pbtBellEmbedding d K) *ᵥ v) =
      ((tensorMultiplicity mu : ℂ) / ((d : ℂ) * tensorMultiplicity alpha)) *
        dotProduct (star u) v := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
