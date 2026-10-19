-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_hilbertMuCompactIsCompact
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.hilbertMuCompactIsCompact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:15:15.180835+00:00
-- url     : https://prove2.me/theorems/e5db7840-3715-4930-a673-68dc7db7f63f
-- title:
--   Proposition 14: Hilbert µ-compact sets are compact
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   If the ambient space is a complete real Hilbert space and $A$ is $\mu$-compact, then
--   $$A\text{ is compact}.$$
--   No convexity assumption is imposed on $A$.
--
--   The source proof may pass to the closed convex hull without changing the theorem’s domain.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 12, Proposition 14: Hilbert µ-compact sets are compact

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section HilbertResults

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [hcomplete : CompleteSpace H]

include hcomplete

/-- Proposition 14, PDF pp.12–13: an admissible µ-compact subset of a
Hilbert space is compact. No convexity hypothesis is imposed. -/
theorem hilbertMuCompactIsCompact (A : Set H) (hA : GeneralBarycenterSpace A)
    (hm : MuCompact A) : IsCompact A := by sorry

end HilbertResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
