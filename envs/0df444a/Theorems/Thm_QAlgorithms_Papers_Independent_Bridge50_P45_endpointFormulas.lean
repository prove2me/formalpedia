-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P45_endpointFormulas
-- name    : QAlgorithms.Papers.Independent.Bridge50.P45.endpointFormulas
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:45:11.937914+00:00
-- url     : https://prove2.me/theorems/f437b535-4bc9-46c9-ac03-49bc3798c11b
-- title:
--   Endpoint limits and explicit endpoint formulas
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, and let $\rho,\sigma$ be nonzero positive semidefinite operators. Powers and the operator logarithm $\widehat{\log}$ are zero on kernels. The labels $t=\{\},*,\flat$ denote the Petz, sandwiched, and log-Euclidean trace functionals, respectively: on positive definite pairs these are $\operatorname{Tr}\rho^\alpha\sigma^{1-\alpha}$, $\operatorname{Tr}(\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2})^\alpha$, and $\operatorname{Tr}\exp(\alpha\log\rho+(1-\alpha)\log\sigma)$. On positive semidefinite pairs they are extended by simultaneous positive regularization. Write $\psi^t_\alpha=\log Q^t_\alpha$ and $D(\rho\|\sigma)=\operatorname{Tr}\rho(\widehat{\log}\rho-\widehat{\log}\sigma)$ with infinite value on support failure. The normalized divergence is $D^t_\alpha=(\psi^t_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ away from one, with normalized relative entropy at one and endpoint limits at zero and infinity. All logarithms are natural and infinite values are retained.
--
--   For every label $t$,
--   $$D^t_0=\lim_{\alpha\downarrow0}D^t_\alpha=\inf_{\alpha>0}D^t_\alpha,\qquad
--   D^t_\infty=\lim_{\alpha\to\infty}D^t_\alpha=\sup_{\alpha>0}D^t_\alpha.$$
--   With $P=\rho^0\wedge\sigma^0$,
--   $$D_0=\log\operatorname{Tr}\rho-\log\operatorname{Tr}\rho^0\sigma,\qquad
--   D^\flat_0=\log\operatorname{Tr}\rho-\log\operatorname{Tr}P\exp(P\widehat{\log}\sigma P).$$
--   If $\rho^0\le\sigma^0$, let $P_r,Q_s$ be the spectral projections of $\rho,\sigma$ at positive eigenvalues $r,s$. Then
--   $$D_\infty=\log\max\{r/s:\operatorname{Tr}P_rQ_s>0\},\qquad
--   D^*_\infty=\log\inf\{\lambda>0:\rho\le\lambda\sigma\},$$
--   $$D^\flat_\infty=\log\inf\{\lambda>0:\widehat{\log}\rho\le\rho^0\widehat{\log}(\lambda\sigma)\rho^0\}
--   =\sup_{\tau\in\mathcal S_\rho}\{D(\tau\|\sigma)-D(\tau\|\rho)\}$$
--   $$=\inf\{\kappa\in\mathbb R:\widehat{\log}\rho-\rho^0\widehat{\log}\sigma\rho^0\le\kappa\rho^0\}.$$
--   The maximum of spectral ratios is attained. The operator inequalities for the b endpoint are understood on the support corner (equivalently, extend both sides by zero outside that corner). If support inclusion fails, every $D^t_\infty$ is $+\infty$.
--
--   No additional formula for star order zero is supplied by this source.
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, PDF p. 13, §III A, unnumbered endpoint formulas (59)–(64)

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

/-- Unnumbered endpoint formulas, PDF pp.13-14 (59)-(64). Includes endpoint
limits and extrema, the Petz maximum, Dmax, and the b support-corner formula.
No additional star-zero formula is invented. -/
theorem endpointFormulas (rho sigma : Mat I) (hrho : NonzeroPSD rho) (hsigma : NonzeroPSD sigma) :
    (∀ t : Flavor,
      Tendsto (fun a : ℝ => renyiValue t a rho sigma) (𝓝[>] 0) (𝓝 (renyiValue t 0 rho sigma)) ∧
      renyiValue t 0 rho sigma = (⨅ a : {a : ℝ // 0 < a}, renyiValue t a.1 rho sigma) ∧
      Tendsto (fun a : ℝ => renyiValue t a rho sigma) atTop (𝓝 (renyiValue t ⊤ rho sigma)) ∧
      renyiValue t ⊤ rho sigma = (⨆ a : {a : ℝ // 0 < a}, renyiValue t a.1 rho sigma)) ∧
    renyiValue .petz 0 rho sigma = (Real.log rho.trace.re : EReal) - traceLog ((support rho * sigma).trace.re) ∧
    renyiValue .b 0 rho sigma = (Real.log rho.trace.re : EReal) -
      traceLog ((meetSupport rho sigma * cfc Real.exp
        (meetSupport rho sigma * lnOp sigma * meetSupport rho sigma)).trace.re) ∧
    (SupportIncluded rho sigma →
      (∃ z : EReal, IsGreatest (spectralRatios rho sigma) z ∧ renyiValue .petz ⊤ rho sigma = traceLog z) ∧
      renyiValue .star ⊤ rho sigma = traceLog (sInf {z : EReal | ∃ l : ℝ,
        0 < l ∧ (((l : ℂ) • sigma) - rho).PosSemidef ∧ z = (l : EReal)}) ∧
      renyiValue .b ⊤ rho sigma = traceLog (sInf {z : EReal | ∃ l : ℝ, 0 < l ∧
        (support rho * lnOp ((l : ℂ) • sigma) * support rho - lnOp rho).PosSemidef ∧ z = (l : EReal)}) ∧
      renyiValue .b ⊤ rho sigma = (⨆ tau : statesOn rho, relativeEntropy tau.1 sigma - relativeEntropy tau.1 rho) ∧
      renyiValue .b ⊤ rho sigma = sInf {z : EReal | ∃ k : ℝ,
        ((k : ℂ) • support rho - (lnOp rho - support rho * lnOp sigma * support rho)).PosSemidef ∧ z = (k : EReal)}) ∧
    (¬ SupportIncluded rho sigma → ∀ t : Flavor, renyiValue t ⊤ rho sigma = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P45

end
