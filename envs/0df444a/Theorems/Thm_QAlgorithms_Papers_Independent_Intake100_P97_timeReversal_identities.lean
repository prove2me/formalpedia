-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_timeReversal_identities
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.timeReversal_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:06:10.928951+00:00
-- url     : https://prove2.me/theorems/e64a323d-fdb6-481b-b471-7ea967d9d84d
-- title:
--   §2.3–2.4 unnumbered: stationary and time-reversal identities
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. Assume (G1): $T_t=D_t^{-1}-D^{-1}$ is trace class for every real $t$ and is differentiable at zero in trace norm. Put $\varsigma=(L^*D^{-1}+D^{-1}L)/2=-\dot T_0/2$ and $\sigma=q_{\varsigma}-\operatorname{tr}(D\varsigma)$, where $q_A$ is the canonical Gaussian quadratic observable. Assume also (G2) and (G3): $0<m<M$ and $mI\le D_t\le MI$ for every real $t$, and $D_t$ converges strongly to $D_+$ and $D_-$ as $t\to+\infty$ and $t\to-\infty$, respectively. Write $\omega_\pm=\omega_{D_\pm}$. Assume (G4): a real unitary involution $\theta$ acts continuously on $X_l$ and satisfies $\theta L=-L\theta$ and $\theta D=D\theta$. Put $p=\omega_+(\sigma)$. Both limiting covariances satisfy $mI\le D_\pm\le MI$ and $LD_\pm+D_\pm L^*=0$. In addition,
--
--   $$D_{-t}=\theta D_t\theta,\quad D_-=\theta D_+\theta,\quad \theta_*\omega_-=\omega_+,\quad\theta\varsigma=-\varsigma\theta,$$
--
--   $$\operatorname{tr}(D\varsigma)=0,\quad\sigma=q_{\varsigma},\quad p=-\omega_-(\sigma)\ge0.$$
--
--   Finally,
--
--   $$p=\lim_{t\to\infty}\frac1t\int_0^t\omega_s(\sigma)\,ds=-\lim_{t\to\infty}\frac1t\operatorname{Ent}(\omega_t\mid\omega).$$
--
--   These are the stationary, time-reversal and steady entropy-production identities.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 6, §2.3–2.4 unnumbered: stationary and time-reversal identities

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Stationarity, reversal identities (11), nonnegative steady production, and
Cesàro/entropy limits, §2.3–2.4, PDF p.6. -/
theorem timeReversal_identities (e : ℕ ≃ G) (l : G → ℝ) (hl : IsWeight l)
    (D L theta : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y))
    (hG1 : G1 D L) (m M : ℝ) (hG2 : G2 D L m M) (hG3 : G3 D L)
    (hG4 : G4 l D L theta) :
    let Dp := futureCovariance D L
    let Dm := pastCovariance D L
    let mean := ∫ x, production e D L x ∂cylinderGaussian Dp
    (∀ v, m * ‖v‖ ^ 2 ≤ inner ℝ v (Dp v) ∧ inner ℝ v (Dp v) ≤ M * ‖v‖ ^ 2 ∧
      m * ‖v‖ ^ 2 ≤ inner ℝ v (Dm v) ∧ inner ℝ v (Dm v) ≤ M * ‖v‖ ^ 2) ∧
    L * Dp + Dp * ContinuousLinearMap.adjoint L = 0 ∧
    L * Dm + Dm * ContinuousLinearMap.adjoint L = 0 ∧
    (∀ t, covarianceAt D L (-t) = theta * covarianceAt D L t * theta) ∧
    Dm = theta * Dp * theta ∧
    (cylinderGaussian Dm).map (weightedTimeReversal l theta) = cylinderGaussian Dp ∧
    theta * productionOperator D L = -(productionOperator D L * theta) ∧
    basisOperatorTrace (D * productionOperator D L) = 0 ∧
    production e D L = gaussianQuadratic e (productionOperator D L) ∧
    mean = -(∫ x, production e D L x ∂cylinderGaussian Dm) ∧ 0 ≤ mean ∧
    Tendsto (fun t => t⁻¹ * ∫ s in (0 : ℝ)..t,
      ∫ x, production e D L x ∂cylinderGaussian (covarianceAt D L s)) atTop (𝓝 mean) ∧
    Tendsto (fun t => -t⁻¹ * (nonpositiveRelativeEntropy (cylinderGaussian (covarianceAt D L t)) (cylinderGaussian D)).toReal)
      atTop (𝓝 mean) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
