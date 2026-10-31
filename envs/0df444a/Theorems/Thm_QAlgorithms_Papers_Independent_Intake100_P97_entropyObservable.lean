-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_entropyObservable
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.entropyObservable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:03:55.554165+00:00
-- url     : https://prove2.me/theorems/227b0e0c-f4ed-4af1-b3ca-8e77af1cf964
-- title:
--   §2.2 unnumbered: entropy observable and trivial invariance criterion
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. Assume (G1): $T_t=D_t^{-1}-D^{-1}$ is trace class for every real $t$ and is differentiable at zero in trace norm. Put $\varsigma=(L^*D^{-1}+D^{-1}L)/2=-\dot T_0/2$ and $\sigma=q_{\varsigma}-\operatorname{tr}(D\varsigma)$, where $q_A$ is the canonical Gaussian quadratic observable. Then $\varsigma$ is self-adjoint and trace class, and the trace-norm derivative is $\dot T_0=-2\varsigma$. The actual observable satisfies
--
--   $$\sigma(x)=q_{\varsigma}(x)-\operatorname{tr}(D\varsigma).$$
--
--   It is integrable for $\omega$, continuous on $K$, and its restriction there is $(x,\varsigma x)-\operatorname{tr}(D\varsigma)$. It is bounded on $X$ exactly when it is identically zero, and this is equivalent to $\omega_t=\omega$ for every real $t$. If only finitely many matrix entries of $\varsigma$ are nonzero, $\sigma$ is continuous on $X$. These properties pin the entropy-production observable used by the fluctuation results.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 5, §2.2 unnumbered: entropy observable and trivial invariance criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Actual entropy observable, trace-norm derivative, integrability, continuity on K,
and triviality criterion; (7)–(8) and the remark, PDF pp.5–6. -/
theorem entropyObservable (e : ℕ ≃ G) (l : G → ℝ) (hl : IsWeight l)
    (D L : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y))
    (hG1 : G1 D L) :
    IsModulusTraceClass (productionOperator D L) ∧
    ContinuousLinearMap.adjoint (productionOperator D L) = productionOperator D L ∧
    HasBilateralTraceDerivative (precisionShift D L) ((-2 : ℝ) • productionOperator D L) 0 ∧
    Integrable (production e D L) (cylinderGaussian D) ∧
    Continuous (fun v : RealCoordinateHilbert G => production e D L (fun i => v i)) ∧
    (∀ v : RealCoordinateHilbert G, production e D L (fun i => v i) =
      inner ℝ v (productionOperator D L v) - basisOperatorTrace (D * productionOperator D L)) ∧
    ((Bornology.IsBounded (Set.range (production e D L))) ↔ production e D L = 0) ∧
    (production e D L = 0 ↔ ∀ t, (cylinderGaussian D).map (flow l L t) = cylinderGaussian D) ∧
    ((∃ I : Finset G, ∀ i j, i ∉ I ∨ j ∉ I → entry (productionOperator D L) i j = 0) →
      Continuous (production e D L)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
