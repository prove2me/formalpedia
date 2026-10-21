-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_convolutionDataProcessing
-- name    : QAlgorithms.Papers.Independent.Next46.P13.convolutionDataProcessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:07:21.707659+00:00
-- url     : https://prove2.me/theorems/294df549-794a-4a6f-8b91-cdc928c0e094
-- title:
--   Lemma 1: convolution data processing
-- statement:
--   Let $d\ge1$ be the number of bosonic modes, and use the canonical Weyl operators $W(\xi)=\exp(i\sqrt{2\pi}\,\xi\cdot\sigma R)$ on the full oscillator Hilbert space. Let $f,g$ be measurable probability densities on $\mathbb R^{2d}$ with full support, let $\rho,\sigma$ be positive trace-class states of trace one and trivial kernel, and let $t\ge0$. Define $f\star_t\rho=\int f(\xi)W(\sqrt t\xi)\rho W(\sqrt t\xi)^\dagger d\xi$. With natural logarithms and relative entropies valued in $[0,+\infty]$,
--
--   $$D(f\star_t\rho\Vert g\star_t\sigma)\le D(f\Vert g)+D(\rho\Vert\sigma).$$
--
--   This is the classical–quantum convolution data-processing inequality. No moment or differentiability assumption is imposed. Full support means every nonempty open subset has positive probability.
--
--   **Formalization Note** The conclusion also certifies the coefficient integrals and normalized output operators, so neither a divergent integral nor an unrealized operator selector supplies a default value.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 11, Lemma 1, (30)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF p.11, Lemma 1: convolution data processing in extended nonnegative reals.
No differentiability or moment restriction is imposed. -/
theorem convolutionDataProcessing {d : ℕ} (hd : 0 < d) (f g : InterleavedPhaseVector d → ℝ)
    (hf : ProbabilityDensity f) (hg : ProbabilityDensity g)
    (hfs : FullSupport f) (hgs : FullSupport g)
    (X Y : CompletedOperator (NumberLabels d)) (hX : IsNormalizedOperator X) (hY : IsNormalizedOperator Y)
    (hXfull : HasTrivialKernel X) (hYfull : HasTrivialKernel Y) (t : ℝ) (ht : 0 ≤ t) :
    WeylRealized d ∧ HybridRealized f t X ∧ HybridRealized g t Y ∧
      quantumD (hybridConvolution f t X) (hybridConvolution g t Y) ≤ classicalRelativeEntropy f g + quantumD X Y := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
