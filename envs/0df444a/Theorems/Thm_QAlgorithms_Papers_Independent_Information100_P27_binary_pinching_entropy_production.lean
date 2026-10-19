-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P27_binary_pinching_entropy_production
-- name    : QAlgorithms.Papers.Independent.Information100.P27.binary_pinching_entropy_production
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:22:01.880811+00:00
-- url     : https://prove2.me/theorems/ef227f31-ceaa-4392-b0e7-4597ea36ec43
-- title:
--   Lemma E.1: binary pinching entropy production
-- statement:
--   Let $B$ be a nonempty finite dimensional system, let $J$ be a Hermitian unitary involution, and let $\theta$ be a full-rank density matrix. Set $\zeta=(\theta+J\theta J)/2$ and $\Xi=\theta-\zeta$. Using entropy in bits, define $f(t)=H(\zeta)-H(\zeta+t\Xi)$ on a neighborhood of $[-1,1]$. Then
--
--   $$
--   f'(1)\ge2f(1).
--   $$
--
--   Full rank supplies the positive-definite neighborhood needed for the ordinary real derivative at $1$. No commutation between $\zeta$ and $\Xi$ is assumed.
-- source:
--   Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, PDF p. 78, Lemma E.1: binary pinching entropy production

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- arXiv:2609.23298v1 PDF pp.78-79, Lemma E.1: binary pinching entropy production.
Positive definiteness encodes precisely the full-rank density hypothesis. -/
theorem binary_pinching_entropy_production {D : Type} [Fintype D] [Nonempty D]
    (J theta : Matrix D D ℂ) (hJherm : Matrix.conjTranspose J = J) (hJinv : J * J = 1)
    (htheta : IsDensityMatrix theta) (hfull : theta.PosDef) :
    2 * pinchingProduction J theta 1 ≤ deriv (pinchingProduction J theta) 1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P27

end
