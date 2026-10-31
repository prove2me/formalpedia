-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_perturbations_case2
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.perturbations_case2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:08:58.519917+00:00
-- url     : https://prove2.me/theorems/b1166f6b-7c47-493b-b2e6-a4d7aa736f4e
-- title:
--   §2.6 Case 2: conserved strictly positive perturbations
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. Assume (G1): $T_t=D_t^{-1}-D^{-1}$ is trace class for every real $t$ and is differentiable at zero in trace norm. Put $\varsigma=(L^*D^{-1}+D^{-1}L)/2=-\dot T_0/2$ and $\sigma=q_{\varsigma}-\operatorname{tr}(D\varsigma)$, where $q_A$ is the canonical Gaussian quadratic observable. Assume also (G2) and (G3): $0<m<M$ and $mI\le D_t\le MI$ for every real $t$, and $D_t$ converges strongly to $D_+$ and $D_-$ as $t\to+\infty$ and $t\to-\infty$, respectively. Write $\omega_\pm=\omega_{D_\pm}$. Assume (G4): a real unitary involution $\theta$ acts continuously on $X_l$ and satisfies $\theta L=-L\theta$ and $\theta D=D\theta$. Let $P$ be bounded self-adjoint and coercively positive, with $\theta P=P\theta$ and $e^{-tL^*}Pe^{-tL}=P$ for every real $t$. For $\lambda>0$ set $D^{\lambda P}=(D^{-1}+\lambda P)^{-1}$ and form all associated objects using the same dynamics. These covariances satisfy (G1)–(G4), with suitable positive scalar bounds in (G2), and
--
--   $$D_+^{\lambda P}=(D_+^{-1}+\lambda P)^{-1},\qquad\varsigma^{\lambda P}=\varsigma,\qquad\sigma^{\lambda P}=\sigma.$$
--
--   Both actual minimal moment domains exhaust the real line: for every $R>0$ there is $\lambda_0>0$ such that, for all $\lambda\ge\lambda_0$,
--
--   $$[-R,R]\subset J^{\lambda P}\cap J^{+\lambda P}.$$
--
--   This is the domain-exhaustion conclusion for conserved strictly positive precision perturbations.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 11, §2.6 Case 2: conserved strictly positive perturbations

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- §2.6 Case 2, PDF p.11: conserved coercive perturbations preserve the
hypotheses and observable, and their actual moment domains exhaust ℝ. The separate
false assertion about the scalar bound δ from (10) is not used and is deferred. -/
theorem perturbations_case2 (e : ℕ ≃ G) (l : G → ℝ) (hl : IsWeight l)
    (D L theta P : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y))
    (hG1 : G1 D L) (m M : ℝ) (hG2 : G2 D L m M) (hG3 : G3 D L)
    (hG4 : G4 l D L theta) (hP : IsCovariance P) (hcomm : theta * P = P * theta)
    (hconserved : ∀ t : ℝ,
      NormedSpace.exp (-t • ContinuousLinearMap.adjoint L) * P * NormedSpace.exp (-t • L) = P) :
    (∀ lambda : ℝ, 0 < lambda →
      let Dp := perturbedCovariance D (lambda • P)
      IsCovariance Dp ∧ G1 Dp L ∧ (∃ mp Mp : ℝ, G2 Dp L mp Mp) ∧
      G3 Dp L ∧ G4 l Dp L theta ∧
      futureCovariance Dp L = perturbedCovariance (futureCovariance D L) (lambda • P) ∧
      productionOperator Dp L = productionOperator D L ∧
      production e Dp L = production e D L) ∧
    (∀ R : ℝ, 0 < R → ∃ lambda0 : ℝ, 0 < lambda0 ∧ ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        Set.Icc (-R) R ⊆ minimalDomain (perturbedCovariance D (lambda • P)) L ∧
        Set.Icc (-R) R ⊆ minimalNessDomain (perturbedCovariance D (lambda • P)) L) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
