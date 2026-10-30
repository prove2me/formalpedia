-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_remark40
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.remark40
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:02:27.904883+00:00
-- url     : https://prove2.me/theorems/cf96dbc5-06fa-40d4-b961-ccf5ce5ea03f
-- title:
--   Remark 40: scalar contraction of block spectral powers
-- statement:
--   Let $N\ge1,d\ge1$, let $\alpha\vdash N-1$, $\mu\vdash N$ be physical compatible shapes, and use the concrete Eq. (145) operator $F_\mu(\alpha)$. Let $P_\alpha$ be the actual central tensor-permutation projector and $m_\lambda$ the actual tensor multiplicities. Define $J u=u\otimes|\Phi^+\rangle$ on the first $N-1$ and final two factors, with the Bell vector normalized. For $u,v$ in the image of $P_\alpha$, and any real $y
--   e0$, let $\rho_\alpha^{-1/y}=\sum_{
--   u\in\alpha}\lambda_
--   u(\alpha)^{-1/y}F_
--   u(\alpha)$ with zero extension off support. Then
--
--   $$\langle Ju,\rho_\alpha^{-1/y}Jv\rangle=c(\alpha,y)\langle u,v\rangle,\qquad
--   c(\alpha,y)=\frac1d\sum_{
--   u\in\alpha}\lambda_
--   u(\alpha)^{-1/y}\frac{m_
--   u}{m_\alpha}.$$
--
--   This is the scalar block contraction of Eqs. (138)–(139), valid also for negative $y$ without inverting a singular full-space operator.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 29, Remark 40: scalar contraction of block spectral powers

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

/-- Remark 40, Eqs.(138)–(139), on a fixed actual alpha block and all nonzero
real y (PDF p.29). The matrix power is zero off support, including for negative y. -/
theorem remark40 {d K : ℕ} (hd : 0 < d) (alpha : Partition d K)
    (y : ℝ) (hy : y ≠ 0) (u v : AliceIndex d K → ℂ)
    (hu : isotypicProjector alpha *ᵥ u = u) (hv : isotypicProjector alpha *ᵥ v = v) :
    dotProduct (star u)
      (((pbtBellEmbedding d K)ᴴ * blockPower alpha (-y⁻¹) * pbtBellEmbedding d K) *ᵥ v) =
      (contractionConstant alpha y : ℂ) * dotProduct (star u) v := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
