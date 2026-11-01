-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P98_channelDistance_sdp
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P98.channelDistance_sdp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:55:14.585098+00:00
-- url     : https://prove2.me/theorems/ed44a161-ecfc-4009-82ff-6f30003309d5
-- title:
--   Channel-distance SDP equals half the diamond norm
-- statement:
--   Let $X=\mathbb C^n$ and $Y=\mathbb C^m$, $n,m\ge1$, and let $\Phi_0,\Phi_1:L(X)\to L(Y)$ be quantum channels, meaning completely positive trace-preserving maps. Put $\Delta=\Phi_0-\Phi_1$ and use the output-first unnormalized Choi matrix $J(\Delta)$. With $D(X)$ denoting positive semidefinite trace-one operators, the two optimization values satisfy
--   $$
--   \sup_{\substack{\rho\in D(X)\\0\preceq W\preceq I_Y\otimes\rho}}\operatorname{Re}\operatorname{Tr}(J(\Delta)^*W)
--   =\inf_{\substack{Z\succeq0\\Z\succeq J(\Delta)}}\|\operatorname{Tr}_Y Z\|_\infty
--   =\frac12\|\Delta\|_\diamond.
--   $$
--   Here the diamond norm uses the full trace norm without a distance factor. This simpler formulation applies to a difference of two channels with the same input and output spaces.
-- source:
--   Semidefinite programs for completely bounded norms, arXiv:0901.4709v2, PDF p. 11, §4, unnumbered: channel-distance SDP has half-diamond value

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P98

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P98

/-- PDF pp.11--12, Section 4: for a difference of TWO CHANNELS both SDP
values equal HALF the diamond norm, with no square. -/
theorem channelDistance_sdp {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (Phi0 Phi1 : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) (h0 : IsChannel Phi0) (h1 : IsChannel Phi1) :
    sSup ((fun v : ℝ => (v : EReal)) '' channelPrimalValues (Phi0 - Phi1)) =
      ((stabilizedTraceNorm (Phi0 - Phi1) / 2 : ℝ) : EReal) ∧
    sInf ((fun v : ℝ => (v : EReal)) '' channelDualValues (Phi0 - Phi1)) =
      ((stabilizedTraceNorm (Phi0 - Phi1) / 2 : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P98

end
