-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P60_compact_quotient_center_finiteRepresentationType
-- name    : QAlgorithms.Papers.Independent.Intake100.P60.compact_quotient_center_finiteRepresentationType
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:09:33.953825+00:00
-- url     : https://prove2.me/theorems/0d0ac291-f905-4841-aa6f-431b534870bd
-- title:
--   Compactness modulo the center implies finite representation type
-- statement:
--   Let $G$ be a Hausdorff locally compact group, let $Z(G)$ be its center, and give $G/Z(G)$ the quotient group topology. If $G/Z(G)$ is compact, then every strongly continuous irreducible unitary representation $\pi$ of $G$ on a nonzero complete complex Hilbert space $H$ satisfies
--
--   $$
--   \dim_{\mathbb C}H<\infty.
--   $$
--
--   Thus $G$ has finite representation type. This permits both $G$ and its center to be noncompact.
-- source:
--   Trace class groups, arXiv:1501.02375v5, PDF p. 13, Examples 3.2, third bullet

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P60

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P60

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

/-- Examples 3.2, third bullet, PDF p.13: compactness of the quotient by the
actual center implies finite representation type. The quotient carries Mathlib's
quotient group topology; compactness of the group or its center is not assumed. -/
theorem compact_quotient_center_finiteRepresentationType
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    [CompactSpace (G ⧸ Subgroup.center G)]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : ContinuousUnitaryRepresentation G H) (hpi : IsTopologicallyIrreducible pi) :
    FiniteDimensional ℂ H := by sorry

end QAlgorithms.Papers.Independent.Intake100.P60

end
