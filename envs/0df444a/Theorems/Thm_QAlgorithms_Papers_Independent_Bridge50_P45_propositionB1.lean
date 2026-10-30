-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_propositionB1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.propositionB1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:41:39.223804+00:00
-- url     : https://prove2.me/theorems/e0d2f3f1-ea1f-4099-a9c2-cd7322103514
-- title:
--   Concavity of generic normalized auxiliary functions
-- statement:
--   Let $X$ be an arbitrary nonempty set, $H$ a nonzero finite-dimensional complex Hilbert space, $W:X\to\mathcal L(H)_+$ a map into nonzero positive semidefinite operators, and $P\in\mathcal P_f(X)$ a finitely supported probability law. Outputs need not have trace one. For a trace functional $Q_\alpha$, define $D_\alpha(A\|B)=[\log Q_\alpha(A\|B)-\log\operatorname{Tr}A]/(\alpha-1)$. Define $\chi_{\alpha,1}$ by minimizing this divergence of the lifted output $\sum_xP(x)|x\rangle\langle x|\otimes W(x)$ against $P\otimes\sigma$, and $\chi_{\alpha,2}$ by minimizing $\sum_xP(x)D_\alpha(W(x)\|\sigma)$, in both cases over output density operators $\sigma$. For $\alpha=(1+s)^{-1}$ put $E_{0,i}(s,W,P)=s\chi_{\alpha,i}(W,P)$. Extended logarithms and extrema retain infinite values.
--
--   Suppose the nonnegative extended trace family $Q_\alpha$ agrees with the classical trace functional on commuting positive pairs, and for every nonzero PSD pair $A,B$ the map $\alpha\mapsto\log Q_\alpha(A\|B)$ is convex on $(0,1)$. Then, for $i=1,2$,
--   $$s\longmapsto E_{0,i}(s,W,P)\quad\text{is concave on }(0,\infty).$$
--
--
--   The normalized first-argument trace is retained even for nonnormalized outputs.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 40, Proposition B.1 Assume that Q(t) is such that for any ̺, σ ∈ L(H)+ , the map α 7→ ψα (̺kσ) is

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

/-- Proposition B.1, PDF pp.39-40: generic Q, exact trace normalization,
unnormalized nonzero PSD outputs, both information types, and s>0. -/
theorem propositionB1 [Nonempty X] [Nonempty I] (Q : TraceFamily) (hclassical : ClassicalAgreement Q)
    (hconvex : ∀ {K : Type} [Fintype K] [DecidableEq K] (rho sigma : Mat K),
      NonzeroPSD rho → NonzeroPSD sigma → EConvexOn (Ioo 0 1) (fun a => traceLog (Q a rho sigma : EReal)))
    (W : X → Mat I) (hW : ∀ x, NonzeroPSD (W x)) (p : X → ℝ) (hp : FiniteInputLaw p)
    (i : Fin 2) : EConcaveOn (Ioi 0) (normalizedAuxiliary Q i W p) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
