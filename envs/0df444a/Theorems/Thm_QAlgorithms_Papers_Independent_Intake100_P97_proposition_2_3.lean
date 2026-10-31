-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_proposition_2_3
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.proposition_2_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:06:40.792867+00:00
-- url     : https://prove2.me/theorems/cfea8542-af31-4ca6-b454-26b7fd729dba
-- title:
--   Proposition 2.3 (all three clauses)
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. Assume (G1): $T_t=D_t^{-1}-D^{-1}$ is trace class for every real $t$ and is differentiable at zero in trace norm. Put $\varsigma=(L^*D^{-1}+D^{-1}L)/2=-\dot T_0/2$ and $\sigma=q_{\varsigma}-\operatorname{tr}(D\varsigma)$, where $q_A$ is the canonical Gaussian quadratic observable. Assume also (G2) and (G3): $0<m<M$ and $mI\le D_t\le MI$ for every real $t$, and $D_t$ converges strongly to $D_+$ and $D_-$ as $t\to+\infty$ and $t\to-\infty$, respectively. Write $\omega_\pm=\omega_{D_\pm}$. Assume (G4): a real unitary involution $\theta$ acts continuously on $X_l$ and satisfies $\theta L=-L\theta$ and $\theta D=D\theta$. Let $\delta_0=m/(M-m)$, $J_t=\{\alpha:D^{-1}+\alpha T_t>0\}$ and $e_t(\alpha)=\log\int_X e^{\alpha\ell_t}\,d\omega$, where $\ell_t=\log(d\omega_t/d\omega)$. An infinite moment gives $e_t(\alpha)=+\infty$. For each $t$ there is $\delta_t\in[\delta_0,+\infty]$ such that
--
--   $$J_t=(-\delta_t,1+\delta_t),\qquad J_{-t}=J_t.$$
--
--   The function $e_t$ is convex on $\mathbb R$, finite exactly on $J_t$, and extends analytically to the union of the upper and lower half-planes with $J_t$. It satisfies $e_t(0)=e_t(1)=0$, $e_t^{\prime}(0)\le0$ and $e_t^{\prime}(1)\ge0$, so it is nonpositive on $[0,1]$ and nonnegative outside. Finally,
--
--   $$e_t(\alpha)=e_t(1-\alpha)\qquad(t,\alpha\in\mathbb R).$$
--
--   This is the finite-time Evans–Searles fluctuation symmetry with the full moment domain.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 7, Proposition 2.3 (all three clauses)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Proposition 2.3, all clauses including extended radii, the cut-plane
analytic extension, and finite-time Evans–Searles symmetry, PDF p.7. -/
theorem proposition_2_3 [Countable G] [Infinite G] (l : G → ℝ) (hl : IsWeight l)
    (D L theta : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y))
    (hG1 : G1 D L) (m M : ℝ) (hG2 : G2 D L m M) (hG3 : G3 D L)
    (hG4 : G4 l D L theta) :
    (∀ t, ∃ r : EReal, ((m / (M - m) : ℝ) : EReal) ≤ r ∧
      gaussianMomentDomain D L t = {alpha : ℝ | (-r) < (alpha : EReal) ∧ (alpha : EReal) < 1 + r}) ∧
    (∀ t, gaussianMomentDomain D L (-t) = gaussianMomentDomain D L t) ∧
    (∀ t alpha, alpha ∈ gaussianMomentDomain D L t →
      gaussianCumulant D L t alpha = (realCumulant D L t alpha : EReal)) ∧
    (∀ t alpha, alpha ∉ gaussianMomentDomain D L t → gaussianCumulant D L t alpha = ⊤) ∧
    (∀ t, ExtendedConvexOn Set.univ (gaussianCumulant D L t)) ∧
    (∀ t, ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (gaussianCutPlane (gaussianMomentDomain D L t)) ∧
      ∀ alpha ∈ gaussianMomentDomain D L t, F (alpha : ℂ) = (realCumulant D L t alpha : ℂ)) ∧
    (∀ t, gaussianCumulant D L t 0 = 0 ∧ gaussianCumulant D L t 1 = 0 ∧
      deriv (realCumulant D L t) 0 ≤ 0 ∧ 0 ≤ deriv (realCumulant D L t) 1) ∧
    (∀ t alpha, alpha ∈ Set.Icc (0 : ℝ) 1 → gaussianCumulant D L t alpha ≤ 0) ∧
    (∀ t alpha, alpha ∉ Set.Icc (0 : ℝ) 1 → 0 ≤ gaussianCumulant D L t alpha) ∧
    (∀ t alpha, gaussianCumulant D L t alpha = gaussianCumulant D L t (1 - alpha)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
