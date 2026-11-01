-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P98_fidelity_sdp_duality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P98.fidelity_sdp_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:58:02.898504+00:00
-- url     : https://prove2.me/theorems/69aad164-034b-4c02-b977-e2a455a4513c
-- title:
--   Numerical Uhlmann–Alberti SDP duality
-- statement:
--   Let $Y=\mathbb C^m$, $Z=\mathbb C^r$, $m,r\ge1$, and let $u,v\in Y\otimes Z$ be arbitrary vectors. Set $P=\operatorname{Tr}_Y(uu^*)$, $Q=\operatorname{Tr}_Y(vv^*)$ and $F(P,Q)=\operatorname{Tr}\sqrt{\sqrt P Q\sqrt P}$. Write $\langle A,B\rangle=\operatorname{Re}\operatorname{Tr}(A^*B)$. The primal and dual problems of PDF page 13 and the two positive-definite infima satisfy
--   $$
--   \sup_{\substack{W\succeq0\\\operatorname{Tr}_Y W\preceq P}}\langle vv^*,W\rangle
--   =\inf_{\substack{H\succeq0\\I_Y\otimes H\succeq vv^*}}\langle P,H\rangle
--   =\inf_{\substack{H\succ0\\\langle Q,H^{-1}\rangle\le1}}\langle P,H\rangle
--   =\inf_{H\succ0}\langle P,H\rangle\langle Q,H^{-1}\rangle
--   =F(P,Q)^2.
--   $$
--   No normalization or minimal-environment assumption is made, and no positive-definite minimizer is asserted. These numerical equalities express the connection between Uhlmann’s and Alberti’s characterizations via SDP duality.
-- source:
--   Semidefinite programs for completely bounded norms, arXiv:0901.4709v2, PDF p. 14, §5, unnumbered: fidelity SDP and Uhlmann–Alberti duality

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P98

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P98

/-- PDF pp.13--15, equation (5) and the constrained PD infimum:
primal, PSD dual, constrained PD dual, and product infimum all have the
squared-fidelity value. This is numerical Uhlmann--Alberti duality, without
Section 3 minimal-rank assumptions or an assertion of a PD minimizer. -/
theorem fidelity_sdp_duality {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (u v : EuclideanSpace ℂ (Fin m × Fin r)) :
    let f := (rootFidelity (traceLeft (pureDensity u)) (traceLeft (pureDensity v))) ^ 2
    sSup ((fun a : ℝ => (a : EReal)) '' fidelityPrimalValues u v) = (f : EReal) ∧
    sInf ((fun a : ℝ => (a : EReal)) '' fidelityDualValues u v) = (f : EReal) ∧
    IsGLB (fidelityPDValues u v) f ∧ IsGLB (fidelityProductValues u v) f := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P98

end
