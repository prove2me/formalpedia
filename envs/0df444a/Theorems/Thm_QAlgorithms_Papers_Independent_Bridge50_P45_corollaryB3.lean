-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_corollaryB3
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.corollaryB3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:43:36.159002+00:00
-- url     : https://prove2.me/theorems/420f6dfe-6113-4f7d-a752-94ad471ae7a0
-- title:
--   Concavity of the explicit Petz auxiliary trace expression
-- statement:
--   Let $X$ be an arbitrary nonempty set, $H$ a nonzero finite-dimensional complex Hilbert space, $W:X\to\mathcal L(H)_+$ a map into nonzero positive semidefinite operators, and $P\in\mathcal P_f(X)$ a finitely supported probability law. Outputs need not have trace one. For a trace functional $Q_\alpha$, define $D_\alpha(A\|B)=[\log Q_\alpha(A\|B)-\log\operatorname{Tr}A]/(\alpha-1)$. Define $\chi_{\alpha,1}$ by minimizing this divergence of the lifted output $\sum_xP(x)|x\rangle\langle x|\otimes W(x)$ against $P\otimes\sigma$, and $\chi_{\alpha,2}$ by minimizing $\sum_xP(x)D_\alpha(W(x)\|\sigma)$, in both cases over output density operators $\sigma$. For $\alpha=(1+s)^{-1}$ put $E_{0,i}(s,W,P)=s\chi_{\alpha,i}(W,P)$. Extended logarithms and extrema retain infinite values.
--
--   The explicit function
--   $$s\longmapsto-\log\operatorname{Tr}\left(\sum_xP(x)W(x)^{1/(1+s)}\right)^{1+s}$$
--   is concave for $s>0$.
--
--   The formula remains valid for nonnormalized outputs, where it differs from normalized E0,1 by an affine trace term.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 40, Corollary B.3 For any map W : X → L(H)+ , and any finitely supported probability distribution

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P45

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

open QAlgorithms.Papers.Independent.Dependency50.P35 (lnOp)

open QAlgorithms.Papers.Independent.Next46.P23 (eigenvalues)

open QAlgorithms (spectralProjector)

variable {I : Type} [Fintype I] [DecidableEq I]

variable {X : Type} [Nonempty X] [Nonempty I]

variable {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]

/-- Corollary B.3, PDF p.40: explicit Petz trace expression, on s>0.
For unnormalized outputs it differs from normalized E0,1 by an affine trace term. -/
theorem corollaryB3 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : ∀ x, NonzeroPSD (W x))
    (p : X → ℝ) (hp : FiniteInputLaw p) :
    EConcaveOn (Ioi 0) (explicitAuxiliary W p) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
