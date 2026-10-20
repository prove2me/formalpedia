-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_hirschmanDensities
-- name    : QAlgorithms.Papers.Independent.Dependency50.P21.hirschmanDensities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:11:20.918371+00:00
-- url     : https://prove2.me/theorems/77e1c836-c4b6-455f-af8e-496fe88ede8f
-- title:
--   Interpolation densities and their limiting recovery density
-- statement:
--   For each θ∈(0,1), the functions αθ and βθ defined in (28) are nonnegative probability densities on the real line. Moreover, for each real t,
--
--   $$\int_{\mathbb R}\alpha_\theta(t)\,dt=\int_{\mathbb R}\beta_\theta(t)\,dt=1,\qquad \lim_{\theta\downarrow0}\beta_\theta(t)=\beta_0(t):=\frac{\pi}{2(\cosh(\pi t)+1)}.$$
--
--   The function β₀ is also a nonnegative, integrable probability density. These normalizations justify averaging the recovery maps with β₀.
-- source:
--   Universal recovery maps and approximate sufficiency of quantum relative entropy, arXiv:1509.07127v3, PDF p. 8, Remark 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P21

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the named interfaces from the pinned accepted paper library.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- Remark 3.3, PDF p.8, Eqs.(29)-(30). All three kernels are probability densities,
and the one-sided limit is theta decreasing to zero through strictly positive values. -/
theorem hirschmanDensities :
    (∀ theta : ℝ, 0 < theta → theta < 1 →
      (∀ t, 0 ≤ alphaDensity theta t ∧ 0 ≤ betaDensity theta t) ∧
      Integrable (alphaDensity theta) ∧ Integrable (betaDensity theta) ∧
      (∫ t : ℝ, alphaDensity theta t) = 1 ∧ (∫ t : ℝ, betaDensity theta t) = 1) ∧
    (∀ t, Tendsto (fun theta : ℝ => betaDensity theta t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (betaZero t))) ∧
    (∀ t, 0 ≤ betaZero t) ∧ Integrable betaZero ∧ (∫ t : ℝ, betaZero t) = 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P21

end
