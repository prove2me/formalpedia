-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_lemma_4_7
-- name    : QAlgorithms.Papers.Independent.Information100.P50.lemma_4_7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:03:12.200538+00:00
-- url     : https://prove2.me/theorems/705e9c67-1f4a-411d-9187-55761d4309fe
-- title:
--   Lemma 4.7: For any continuous g:[0,1]→R, omega_g(delta) tends to 0 as delta↓0, uniformly over matrix dimensions
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For every continuous $g:[0,1]\to\mathbb R$, the defining set for the operator modulus is nonempty and bounded above at each $\delta\ge0$, and
--
--   $$\omega_g(\delta)\longrightarrow0\qquad(\delta\downarrow0).$$
--
--   The supremum defining $\omega_g$ is over all finite matrix sizes and pairs of effects at operator distance at most $\delta$. This also holds for every mean perspective $g_\sigma$, and for $h_f(t)=(1-t)f(t/(1-t))$ with $h_f(0)=f(0+)$ and $h_f(1)=f'(\infty)$ for every bounded operator-convex generator $f$ with $f(1)=0$. Continuity of these two special scalar functions is a conclusion. This ensures a dimension-independent modulus actually vanishes at zero.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 15, Lemma 4.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Lemma 4.7, source PDF pp.15–16. Nonemptiness and boundedness record that the real
supremum defining the modulus is legitimate. Special-case continuity is a conclusion. -/
theorem lemma_4_7 :
    (∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 1) →
      (∀ delta ≥ (0 : ℝ), (modulusValues g delta).Nonempty ∧ BddAbove (modulusValues g delta)) ∧
      Tendsto (operatorModulus g) (𝓝[≥] (0 : ℝ)) (𝓝 0)) ∧
    (∀ s : Mean, ContinuousOn (meanPerspective s) (Icc 0 1) ∧
      Tendsto (operatorModulus (meanPerspective s)) (𝓝[≥] (0 : ℝ)) (𝓝 0)) ∧
    (∀ f : BoundedGenerator, ContinuousOn (convexPerspective f.f) (Icc 0 1) ∧
      Tendsto (operatorModulus (convexPerspective f.f)) (𝓝[≥] (0 : ℝ)) (𝓝 0)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
