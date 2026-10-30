-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_corollaryB2
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.corollaryB2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:42:41.003809+00:00
-- url     : https://prove2.me/theorems/9790d1df-e6b8-4fee-b65f-df38a56004f0
-- title:
--   Positive-s concavity for all three auxiliary families
-- statement:
--   Let $X$ be an arbitrary nonempty set, $H$ a nonzero finite-dimensional complex Hilbert space, $W:X\to\mathcal L(H)_+$ a map into nonzero positive semidefinite operators, and $P\in\mathcal P_f(X)$ a finitely supported probability law. Outputs need not have trace one. For a trace functional $Q_\alpha$, define $D_\alpha(A\|B)=[\log Q_\alpha(A\|B)-\log\operatorname{Tr}A]/(\alpha-1)$. Define $\chi_{\alpha,1}$ by minimizing this divergence of the lifted output $\sum_xP(x)|x\rangle\langle x|\otimes W(x)$ against $P\otimes\sigma$, and $\chi_{\alpha,2}$ by minimizing $\sum_xP(x)D_\alpha(W(x)\|\sigma)$, in both cases over output density operators $\sigma$. For $\alpha=(1+s)^{-1}$ put $E_{0,i}(s,W,P)=s\chi_{\alpha,i}(W,P)$. Extended logarithms and extrema retain infinite values.
--
--   For each of the Petz, sandwiched, and log-Euclidean trace families and each $i=1,2$,
--   $$s\longmapsto E^t_{0,i}(s,W,P)\quad\text{is concave on }(0,\infty).$$
--
--
--   This inherits the positive-s domain from B.1 and makes no negative-s assertion for Petz or star.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 40, Corollary B.2 By Lemma III.12, Qα with (t) = { }, (t) = ∗, (t) = ♭ satisfy the convexity assumption

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

/-- Corollary B.2, PDF p.40: positive-s concavity for each of the three families,
with no trace-one assumption on outputs. -/
theorem corollaryB2 [Nonempty X] [Nonempty I] (t : Flavor) (W : X → Mat I) (hW : ∀ x, NonzeroPSD (W x))
    (p : X → ℝ) (hp : FiniteInputLaw p) (i : Fin 2) :
    EConcaveOn (Ioi 0) (normalizedAuxiliary (fun a rho sigma => asNN (regularizedTrace t a rho sigma)) i W p) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
