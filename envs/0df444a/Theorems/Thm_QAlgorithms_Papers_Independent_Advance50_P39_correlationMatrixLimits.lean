-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P39_correlationMatrixLimits
-- name    : QAlgorithms.Papers.Independent.Advance50.P39.correlationMatrixLimits
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:00:28.669234+00:00
-- url     : https://prove2.me/theorems/90a8b65e-9fa8-4317-919c-7c7dc0fa769f
-- title:
--   Spatial correlation matrices tend to the two stated endpoints
-- statement:
--   Let $N\ge1$ and let $R_{mn}$ be the intermolecular distances for $N$ distinct sites, with $R_{mm}=0$ and $R_{mn}>0$ when $m\ne n$. For positive correlation radius $R_c$, define $C_{mn}(R_c)=\exp(-R_{mn}/R_c)$. Entrywise,
--   $$
--   \lim_{R_c\downarrow0}C_{mn}(R_c)=\delta_{mn},\qquad
--   \lim_{R_c\to\infty}C_{mn}(R_c)=1.
--   $$
--   These are the uncorrelated and perfectly correlated matrix limits. The first is a one-sided limit; assigning the totalized real quotient a value at $R_c=0$ would not represent the physical endpoint.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, PDF p. 5, §IV: limiting spatial correlation matrices

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4--5, §IV: uncorrelated and perfectly correlated limits.
At radius zero use the right-hand limit, never real division by zero. -/
theorem correlationMatrixLimits {n : ℕ} (hn : 0 < n)
    (distance : Fin n → Fin n → ℝ) (hdiag : ∀ i, distance i i = 0)
    (hoffdiag : ∀ i j, i ≠ j → 0 < distance i j) :
    (∀ i j, Tendsto (fun radius => spatialCorrelation (distance i j) radius)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (if i = j then 1 else 0))) ∧
    (∀ i j, Tendsto (fun radius => spatialCorrelation (distance i j) radius)
      atTop (nhds 1)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P39

end
