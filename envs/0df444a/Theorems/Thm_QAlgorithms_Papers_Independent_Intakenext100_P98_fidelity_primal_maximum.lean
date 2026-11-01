-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P98_fidelity_primal_maximum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P98.fidelity_primal_maximum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:56:41.472603+00:00
-- url     : https://prove2.me/theorems/abeb3f9d-9038-4659-b104-54b37e5443af
-- title:
--   Fidelity squared is an attained primal SDP value
-- statement:
--   Let $Y=\mathbb C^m$ and $Z=\mathbb C^r$, where $m,r\ge1$, and let $u,v\in Y\otimes Z$ be arbitrary vectors. Define $P=\operatorname{Tr}_Y(uu^*)$ and $Q=\operatorname{Tr}_Y(vv^*)$, and let $F(P,Q)=\operatorname{Tr}\sqrt{\sqrt P Q\sqrt P}$ denote root fidelity. Then
--   $$
--   F(P,Q)^2=\max_{\substack{W\succeq0\\\operatorname{Tr}_Y W\preceq P}}\operatorname{Re}\operatorname{Tr}((vv^*)^*W).
--   $$
--   The maximum is attained. Neither vector must have norm one, and the marginal constraint is an inequality. This is the primal fidelity SDP obtained from Uhlmann’s theorem.
-- source:
--   Semidefinite programs for completely bounded norms, arXiv:0901.4709v2, PDF p. 14, Corollary 7 (fidelity as a primal SDP maximum)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P98

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P98

/-- PDF p.14, Corollary 7: squared fidelity is a MAXIMUM with a marginal
INEQUALITY; P,Q are constructed from the given, unnormalized vectors. -/
theorem fidelity_primal_maximum {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (u v : EuclideanSpace ℂ (Fin m × Fin r)) :
    IsGreatest (fidelityPrimalValues u v)
      ((rootFidelity (traceLeft (pureDensity u)) (traceLeft (pureDensity v))) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P98

end
