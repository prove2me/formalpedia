-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_infinity_centre_outside_segment
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.infinity_centre_outside_segment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:55:09.089978+00:00
-- url     : https://prove2.me/theorems/ff2b0a5b-0458-40d1-94ea-e0e27dbdb24f
-- title:
--   Unnumbered: an infinity-centre outside the convex hull
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. On $\mathbb C^3$ take diagonal density matrices with diagonals $\rho_1=(1/2,1/4,1/4)$, $\rho_2=(1/2,1/6,1/3)$ and $\sigma_*=(6/13,3/13,4/13)$. Let $S_\infty$ be the limit of $S_\alpha$ as $\alpha\to\infty$, and let $R_\infty$ minimize the maximum divergence over all density centres. Then
--
--   $$\max_{i=1,2}S_\infty(\rho_i\|\sigma_*)=R_\infty(\{\rho_1,\rho_2\}),$$
--
--   whereas for every $t\in[0,1]$ the centre $(1-t)\rho_1+t\rho_2$ does not attain that radius. Thus an infinity-centre exists outside the segment and no centre lies on the segment; the optimization is not restricted to diagonal centres.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 10, Unnumbered: an infinity-centre outside the convex hull

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- The explicit infinity-centre outside the convex hull, PDF p.10.
The full radius optimizes over all density matrices, not just diagonal ones. -/
theorem infinity_centre_outside_segment :
    let W := pairFamily exampleFirst exampleSecond
    IsDensityMatrix exampleFirst ∧ IsDensityMatrix exampleSecond ∧ IsDensityMatrix exampleCentre ∧
    (⨆ i : Fin 2, infinityRelative (W i) exampleCentre) = divergenceRadiusBits infinityRelative W ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (⨆ i : Fin 2, infinityRelative (W i) (AffineMap.lineMap exampleFirst exampleSecond t)) ≠
        divergenceRadiusBits infinityRelative W) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
