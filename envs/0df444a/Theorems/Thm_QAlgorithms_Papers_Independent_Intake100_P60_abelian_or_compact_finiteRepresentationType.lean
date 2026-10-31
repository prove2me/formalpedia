-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P60_abelian_or_compact_finiteRepresentationType
-- name    : QAlgorithms.Papers.Independent.Intake100.P60.abelian_or_compact_finiteRepresentationType
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:08:05.065619+00:00
-- url     : https://prove2.me/theorems/4539f56b-7d9e-49be-aa3b-a0177df1dc0d
-- title:
--   Abelian and compact groups have finite representation type
-- statement:
--   Let $G$ be a Hausdorff locally compact group. Suppose that $G$ is abelian or compact. For every strongly continuous irreducible unitary representation $\pi$ of $G$ on a nonzero complete complex Hilbert space $H$,
--
--   $$
--   \dim_{\mathbb C}H<\infty.
--   $$
--
--   Thus $G$ has finite representation type, meaning that each of its irreducible unitary representations is finite-dimensional. No common bound on their dimensions is asserted. Irreducibility excludes only proper nonzero closed invariant complex subspaces.
-- source:
--   Trace class groups, arXiv:1501.02375v5, PDF p. 12, Examples 3.2, first bullet

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P60

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P60

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

/-- Examples 3.2, first bullet, PDF p.12: abelian groups and compact groups
are of finite representation type. The universally quantified carrier H and
representation pi expand Definition 3.1 without restricting their dimensions. -/
theorem abelian_or_compact_finiteRepresentationType
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (hG : (∀ a b : G, a * b = b * a) ∨ IsCompact (Set.univ : Set G))
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : ContinuousUnitaryRepresentation G H) (hpi : IsTopologicallyIrreducible pi) :
    FiniteDimensional ℂ H := by sorry

end QAlgorithms.Papers.Independent.Intake100.P60

end
