-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_proposition_2_2
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.proposition_2_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:05:19.622596+00:00
-- url     : https://prove2.me/theorems/c9de747c-e7ca-4e5b-b3fb-7385f12a724b
-- title:
--   Proposition 2.2 (both directions of time)
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. Assume (G1): $T_t=D_t^{-1}-D^{-1}$ is trace class for every real $t$ and is differentiable at zero in trace norm. Put $\varsigma=(L^*D^{-1}+D^{-1}L)/2=-\dot T_0/2$ and $\sigma=q_{\varsigma}-\operatorname{tr}(D\varsigma)$, where $q_A$ is the canonical Gaussian quadratic observable. Assume also (G2) and (G3): $0<m<M$ and $mI\le D_t\le MI$ for every real $t$, and $D_t$ converges strongly to $D_+$ and $D_-$ as $t\to+\infty$ and $t\to-\infty$, respectively. Write $\omega_\pm=\omega_{D_\pm}$. For every bounded continuous real function $f$ on $X$,
--
--   $$\lim_{t\to\pm\infty}\omega_t(f)=\omega_\pm(f).$$
--
--   Moreover, $\sigma$ is integrable for both limiting laws and
--
--   $$\omega_\pm(\sigma)=\lim_{t\to\pm\infty}\omega_t(\sigma)=\operatorname{tr}(\varsigma(D_\pm-D)).$$
--
--   This is Gaussian weak convergence together with convergence of the unbounded canonical quadratic observable.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 6, Proposition 2.2 (both directions of time)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Proposition 2.2, weak convergence and the integrable quadratic expectation in
both time directions, under (G1)–(G3) only, PDF p.6. -/
theorem proposition_2_2 (e : ℕ ≃ G) (l : G → ℝ) (hl : IsWeight l)
    (D L : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y))
    (hG1 : G1 D L) (m M : ℝ) (hG2 : G2 D L m M) (hG3 : G3 D L) :
    (∀ f : CylinderPhase G → ℝ, Continuous f → Bornology.IsBounded (Set.range f) →
      Tendsto (fun t => ∫ x, f x ∂cylinderGaussian (covarianceAt D L t)) atTop
        (𝓝 (∫ x, f x ∂cylinderGaussian (futureCovariance D L))) ∧
      Tendsto (fun t => ∫ x, f x ∂cylinderGaussian (covarianceAt D L t)) atBot
        (𝓝 (∫ x, f x ∂cylinderGaussian (pastCovariance D L)))) ∧
    Integrable (production e D L) (cylinderGaussian (futureCovariance D L)) ∧
    Integrable (production e D L) (cylinderGaussian (pastCovariance D L)) ∧
    Tendsto (fun t => ∫ x, production e D L x ∂cylinderGaussian (covarianceAt D L t)) atTop
      (𝓝 (∫ x, production e D L x ∂cylinderGaussian (futureCovariance D L))) ∧
    Tendsto (fun t => ∫ x, production e D L x ∂cylinderGaussian (covarianceAt D L t)) atBot
      (𝓝 (∫ x, production e D L x ∂cylinderGaussian (pastCovariance D L))) ∧
    (∫ x, production e D L x ∂cylinderGaussian (futureCovariance D L)) =
      basisOperatorTrace (productionOperator D L * (futureCovariance D L - D)) ∧
    (∫ x, production e D L x ∂cylinderGaussian (pastCovariance D L)) =
      basisOperatorTrace (productionOperator D L * (pastCovariance D L - D)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
