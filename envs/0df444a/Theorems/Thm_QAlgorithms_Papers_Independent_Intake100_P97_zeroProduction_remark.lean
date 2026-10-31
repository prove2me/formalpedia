-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_zeroProduction_remark
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.zeroProduction_remark
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:08:20.094106+00:00
-- url     : https://prove2.me/theorems/951c415a-704d-4e76-823a-92040c459239
-- title:
--   Theorem 2.4 Remark 1: zero production and vanishing cumulant
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. Assume (G1): $T_t=D_t^{-1}-D^{-1}$ is trace class for every real $t$ and is differentiable at zero in trace norm. Put $\varsigma=(L^*D^{-1}+D^{-1}L)/2=-\dot T_0/2$ and $\sigma=q_{\varsigma}-\operatorname{tr}(D\varsigma)$, where $q_A$ is the canonical Gaussian quadratic observable. Assume also (G2) and (G3): $0<m<M$ and $mI\le D_t\le MI$ for every real $t$, and $D_t$ converges strongly to $D_+$ and $D_-$ as $t\to+\infty$ and $t\to-\infty$, respectively. Write $\omega_\pm=\omega_{D_\pm}$. Assume (G4): a real unitary involution $\theta$ acts continuously on $X_l$ and satisfies $\theta L=-L\theta$ and $\theta D=D\theta$. Write $p_\pm=\omega_\pm(\sigma)$. If $\omega_-=\omega_+$, then $p_+=p_-=0$. If either $p_+=0$ or $p_-=0$, the reference limiting cumulant vanishes on its entire open domain $J$, and its analytic extension to the cut plane is identically zero. In particular,
--
--   $$\lim_{t\to\infty}\frac{e_t(\alpha)}{t}=0\qquad(\alpha\in J),\qquad [0,1]\subset J.$$
--
--   This relates equality of limiting laws to zero production and zero limiting reference cumulants in the stated directions.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 8, Theorem 2.4 Remark 1: zero production and vanishing cumulant

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Theorem 2.4 Remark 1, PDF p.8. Equality of the two limiting measures implies
zero production; either zero mean implies a vanishing limiting cumulant on its
open domain. No converse equality of limiting measures is asserted. -/
theorem zeroProduction_remark (e : ℕ ≃ G) (l : G → ℝ) (hl : IsWeight l)
    (D L theta : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y))
    (hG1 : G1 D L) (m M : ℝ) (hG2 : G2 D L m M) (hG3 : G3 D L)
    (hG4 : G4 l D L theta) :
    let meanp := ∫ x, production e D L x ∂cylinderGaussian (futureCovariance D L)
    let meanm := ∫ x, production e D L x ∂cylinderGaussian (pastCovariance D L)
    (cylinderGaussian (pastCovariance D L) = cylinderGaussian (futureCovariance D L) →
      meanp = 0 ∧ meanm = 0) ∧
    ((meanp = 0 ∨ meanm = 0) →
      Set.Icc (0 : ℝ) 1 ⊆ minimalDomain D L ∧
      (∀ alpha ∈ minimalDomain D L,
        Tendsto (fun t => t⁻¹ * realCumulant D L t alpha) atTop (𝓝 0)) ∧
      (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (gaussianCutPlane (minimalDomain D L)) ∧
        (∀ z ∈ gaussianCutPlane (minimalDomain D L), F z = 0) ∧
        ∀ alpha ∈ minimalDomain D L,
          Tendsto (fun t => (t⁻¹ * realCumulant D L t alpha : ℝ)) atTop
            (𝓝 (F (alpha : ℂ)).re))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
