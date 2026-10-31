-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_measurableGaussian_flow
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.measurableGaussian_flow
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:02:14.46479+00:00
-- url     : https://prove2.me/theorems/d08768c2-e9af-442c-b173-bd7227094960
-- title:
--   §2.1–2.2 unnumbered: measurable flow and evolved Gaussian covariance
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. The extension is continuous and agrees with $L$ on $K$. The map $(t,x)\mapsto\phi^t x$ is measurable, $\phi^0=\mathrm{id}$, and $\phi^{s+t}=\phi^s\circ\phi^t$. Each $\phi^t$ is a measurable bijection with measurable inverse $\phi^{-t}$. On one set of full $\omega_D$ measure, the weighted exponential formula holds for every real time. Finally,
--
--   $$(\phi^t)_*\omega_D=\omega_{e^{tL}De^{tL^*}},\qquad \omega_{D_t}(X\setminus X_l)=0.$$
--
--   Every $D_t$ is a covariance. These identities connect the constructed measurable dynamics with its Gaussian evolution.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 4, §2.1–2.2 unnumbered: measurable flow and evolved Gaussian covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Continuous weighted extension, piecewise measurable automorphism group, and
Gaussian pushforward covariance; (6) and §2.2, PDF pp.4–5. -/
theorem measurableGaussian_flow [Countable G] [Infinite G] (l : G → ℝ) (hl : IsWeight l)
    (D L : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y)) :
    WeightedCompatible l L ∧ ExtendsWeighted l L (weightedExtension l L) ∧
    Measurable (fun p : ℝ × CylinderPhase G => flow l L p.1 p.2) ∧
    (∀ x, flow l L 0 x = x) ∧
    (∀ s t x, flow l L (s + t) x = flow l L s (flow l L t x)) ∧
    (∀ t, Measurable (flow l L t) ∧ Function.Bijective (flow l L t)) ∧
    (∀ t x, ¬ inWeighted l x → flow l L t x = x) ∧
    (∀ᵐ x ∂cylinderGaussian D, ∀ t, flow l L t x =
      weightedPhase l ((NormedSpace.exp (t • weightedExtension l L)) (weightedVector l x))) ∧
    (∀ t, IsCovariance (covarianceAt D L t) ∧
      (cylinderGaussian D).map (flow l L t) = cylinderGaussian (covarianceAt D L t) ∧
      cylinderGaussian (covarianceAt D L t) {x | ¬ inWeighted l x} = 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
