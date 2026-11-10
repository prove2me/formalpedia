-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_measurable_spectral_bijection
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.measurable_spectral_bijection
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T07:32:39.132727+00:00
-- url     : https://prove2.me/theorems/01dc4f67-6524-49e5-8e11-bae25c70f987
-- title:
--   measurable-spectral-bijection
-- statement:
--   Let $M$ be nonempty and equipped with a concrete sigma algebra. Measurable real functions and right-continuous spectral families of measurable subsets are in bijection under
--
--   $$g\longmapsto\sigma_g(\lambda)=g^{-1}(({-\infty},\lambda]),\qquad \sigma\longmapsto g_\sigma(x)=\inf\{\lambda:x\in\sigma(\lambda)\}.$$
--
--   The cuts are nonempty and bounded below at every point. The induced function is measurable, its closed sublevels equal the original family, and both displayed constructions are inverse. No boundedness is imposed on $g$.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 12, measurable-spectral-bijection

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- measurable-spectral-bijection; de Groote, Observables I, PDF p./pp. 12.
-/
theorem measurable_spectral_bijection {M : Type u} [Nonempty M] [MeasurableSpace M] :
    (∀ g : M → ℝ, Measurable g → IsMeasurableSpectralFamily (measurableSublevels g) ∧
      spectralCutInfimum (measurableSublevels g) = g) ∧
    (∀ E : ℝ → Set M, IsMeasurableSpectralFamily E →
      Measurable (spectralCutInfimum E) ∧ measurableSublevels (spectralCutInfimum E) = E ∧
      ∀ x : M, {t | x ∈ E t}.Nonempty ∧ BddBelow {t | x ∈ E t}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
