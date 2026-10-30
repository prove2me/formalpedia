-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_propositionB5
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.propositionB5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:44:26.377996+00:00
-- url     : https://prove2.me/theorems/3256e99b-8122-43fb-a125-86706b7ca658
-- title:
--   Negative-s concavity of b auxiliary functions
-- statement:
--   Let $X$ be an arbitrary nonempty set, $H$ a nonzero finite-dimensional complex Hilbert space, $W:X\to\mathcal L(H)_+$ a map into nonzero positive semidefinite operators, and $P\in\mathcal P_f(X)$ a finitely supported probability law. Outputs need not have trace one. For a trace functional $Q_\alpha$, define $D_\alpha(A\|B)=[\log Q_\alpha(A\|B)-\log\operatorname{Tr}A]/(\alpha-1)$. Define $\chi_{\alpha,1}$ by minimizing this divergence of the lifted output $\sum_xP(x)|x\rangle\langle x|\otimes W(x)$ against $P\otimes\sigma$, and $\chi_{\alpha,2}$ by minimizing $\sum_xP(x)D_\alpha(W(x)\|\sigma)$, in both cases over output density operators $\sigma$. For $\alpha=(1+s)^{-1}$ put $E_{0,i}(s,W,P)=s\chi_{\alpha,i}(W,P)$. Extended logarithms and extrema retain infinite values.
--
--   For the log-Euclidean trace family and $i=1,2$,
--   $$s\longmapsto E^\flat_{0,i}(s,W,P)\quad\text{is concave on }(-1,0).$$
--
--
--   This is the negative-s, equivalently above-one-order, assertion for the b family only.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 40, Proposition B.5 For any map W : X → L(H)+ , and any finitely supported probability distribution

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

/-- Proposition B.5, PDF p.40: negative-s concavity only for the b family;
both information types and unnormalized nonzero PSD outputs are retained. -/
theorem propositionB5 [Nonempty X] [Nonempty I] (W : X → Mat I) (hW : ∀ x, NonzeroPSD (W x))
    (p : X → ℝ) (hp : FiniteInputLaw p) (i : Fin 2) :
    EConcaveOn (Ioo (-1) 0) (normalizedAuxiliary (fun a rho sigma => asNN (regularizedTrace .b a rho sigma)) i W p) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
