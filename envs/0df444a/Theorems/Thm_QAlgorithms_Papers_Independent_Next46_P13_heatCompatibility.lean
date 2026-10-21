-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_heatCompatibility
-- name    : QAlgorithms.Papers.Independent.Next46.P13.heatCompatibility
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:09:07.435719+00:00
-- url     : https://prove2.me/theorems/63e5d265-4c5f-4517-9114-04e4f5d3849a
-- title:
--   Lemma 5: compatibility of heat semigroups
-- statement:
--   Let $d\ge1$, let $f$ be a measurable probability density on $\mathbb R^{2d}$, and let $\rho$ be a normalized positive trace-class bosonic state with trivial kernel. Let $L_{\rm heat}=-\pi\sum_{j=1}^{2d}[R_j,[R_j,\cdot]]$ and $C_c=\frac12\Delta$, using the Weyl normalization $W(\xi)=\exp(i\sqrt{2\pi}\,\xi\cdot\sigma R)$ and the displacement convolution $\star_t$. For $t,\mu,\nu\ge0$ and $\xi=\mu+t\nu$,
--
--   $$e^{\xi L_{\rm heat}}(f\star_t\rho)=e^{\nu C_c}(f)\star_t e^{\mu L_{\rm heat}}(\rho).$$
--
--   This is compatibility of independent classical and quantum heat flows with the hybrid convolution. Zero times are identity maps; no singular zero-variance Gaussian density is used. The symbols $\mu,\nu$ here are independent heat times.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 15, Lemma 5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF p.15, Lemma 5: independent nonnegative heat times, including zero times. -/
theorem heatCompatibility {d : ℕ} (hd : 0 < d) (f : InterleavedPhaseVector d → ℝ)
    (hf : ProbabilityDensity f) (X : CompletedOperator (NumberLabels d)) (hX : IsNormalizedOperator X)
    (hXfull : HasTrivialKernel X) (t mu nu : ℝ) (ht : 0 ≤ t) (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) :
    WeylRealized d ∧ ProbabilityDensity (classicalHeat nu f) ∧
      HybridRealized f t X ∧ HybridRealized (standardGaussian d) mu X ∧
      HybridRealized (standardGaussian d) (mu + t * nu) (hybridConvolution f t X) ∧
      HybridRealized (classicalHeat nu f) t (gaussianHeatFlow mu X) ∧
      gaussianHeatFlow (mu + t * nu) (hybridConvolution f t X) = hybridConvolution (classicalHeat nu f) t (gaussianHeatFlow mu X) := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
