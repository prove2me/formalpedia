-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_petz_derivatives_convexity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.petz_derivatives_convexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:40:59.233157+00:00
-- url     : https://prove2.me/theorems/bec1da39-3886-4ebd-a0b5-20df299dd660
-- title:
--   Lemma 1: Petz log-overlap derivatives and convexity
-- statement:
--   Let $\rho,\sigma$ be faithful density matrices on a nonzero finite-dimensional complex Hilbert space. For real $s$ define $\Psi(s)=\log\operatorname{Tr}(\rho^s\sigma^{1-s})$, using its real spectral extension. Set $D(\rho\Vert\sigma)=\operatorname{Tr}\rho(\log\rho-\log\sigma)$ and $V(\rho\Vert\sigma)=\operatorname{Tr}\rho(\log\rho-\log\sigma)^2-D(\rho\Vert\sigma)^2$. Then
--   $$\Psi'(0)=-D(\sigma\Vert\rho),\qquad\Psi'(1)=D(\rho\Vert\sigma),\qquad\Psi''(1)=V(\rho\Vert\sigma).$$
--   Moreover, $\Psi''(s)\ge0$ for every $s\in[0,1]$, and $\Psi$ is convex on $[0,1]$.
--
--   These identities connect the Petz logarithm with the entropy and information variance. Endpoint derivatives are derivatives of the extension, with no truncation to $[0,1]$.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 6, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Lemma 1, PDF p.6: all three derivative identities and both convexity clauses.
Derivatives use the real spectral extension, not a function truncated to [0,1]. -/
theorem petz_derivatives_convexity [Nonempty I] (rho sigma : Mat I)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (hfaithfulRho : rho.PosDef) (hfaithfulSigma : sigma.PosDef) :
    deriv (realPetzLogOverlap rho sigma) 0 = -finitePairRelativeEntropyNats sigma rho ∧
    deriv (realPetzLogOverlap rho sigma) 1 = finitePairRelativeEntropyNats rho sigma ∧
    deriv (deriv (realPetzLogOverlap rho sigma)) 1 = pairInformationVarianceNats rho sigma ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ deriv (deriv (realPetzLogOverlap rho sigma)) s) ∧
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (realPetzLogOverlap rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
