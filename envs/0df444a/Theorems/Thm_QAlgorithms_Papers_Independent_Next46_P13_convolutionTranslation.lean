-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_convolutionTranslation
-- name    : QAlgorithms.Papers.Independent.Next46.P13.convolutionTranslation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:08:21.01084+00:00
-- url     : https://prove2.me/theorems/bd0c531b-0e39-40f2-8ae2-2aed5705e6d3
-- title:
--   Lemma 2: translation covariance
-- statement:
--   Let $d\ge1$, let $f$ be a measurable probability density on $\mathbb R^{2d}$, and let $\rho$ be a normalized positive trace-class bosonic state with trivial kernel. Use $W(\xi)=\exp(i\sqrt{2\pi}\,\xi\cdot\sigma R)$ and define $\rho^{(v)}=W(v)\rho W(v)^\dagger$, $f^{(v)}(x)=f(x-v)$ and the displacement average $f\star_t\rho$. For $\omega_q,\omega_c>0$, $t\ge0$, and every $\theta\in\mathbb R^{2d}$, put $\omega=\omega_q+\sqrt t\,\omega_c$. Then
--
--   $$(f\star_t\rho)^{(\omega\theta)}=f^{(\omega_c\theta)}\star_t\rho^{(\omega_q\theta)}.$$
--
--   This identifies the separate classical and quantum translations comprising a translation of the output. The positive-weight domain is exactly the printed lemma's domain, and $t=0$ is included.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 11, Lemma 2, (32)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF pp.11–12, Lemma 2, (32): preserve the printed positive-weight domain. -/
theorem convolutionTranslation {d : ℕ} (hd : 0 < d) (f : InterleavedPhaseVector d → ℝ)
    (hf : ProbabilityDensity f) (X : CompletedOperator (NumberLabels d)) (hX : IsNormalizedOperator X)
    (hXfull : HasTrivialKernel X) (omegaQ omegaC t : ℝ)
    (hq : 0 < omegaQ) (hc : 0 < omegaC) (ht : 0 ≤ t) (theta : InterleavedPhaseVector d) :
    WeylRealized d ∧ HybridRealized f t X ∧
      HybridRealized (densityTranslate (omegaC • theta) f) t (translated (omegaQ • theta) X) ∧
      translated ((omegaQ + Real.sqrt t * omegaC) • theta) (hybridConvolution f t X) =
        hybridConvolution (densityTranslate (omegaC • theta) f) t (translated (omegaQ • theta) X) := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
