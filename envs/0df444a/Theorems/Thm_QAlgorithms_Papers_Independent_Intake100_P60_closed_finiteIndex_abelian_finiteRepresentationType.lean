-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P60_closed_finiteIndex_abelian_finiteRepresentationType
-- name    : QAlgorithms.Papers.Independent.Intake100.P60.closed_finiteIndex_abelian_finiteRepresentationType
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:08:48.516371+00:00
-- url     : https://prove2.me/theorems/dcf36da9-5da3-4e88-8631-773d4d29b1ef
-- title:
--   A closed abelian subgroup of finite index implies finite representation type
-- statement:
--   Let $G$ be a Hausdorff locally compact group, and let $A\leq G$ be a closed abelian subgroup of finite index. Every strongly continuous irreducible unitary representation $\pi$ of $G$ on a nonzero complete complex Hilbert space $H$ satisfies
--
--   $$
--   \dim_{\mathbb C}H<\infty.
--   $$
--
--   Consequently, $G$ has finite representation type. The supplied subgroup $A$ need not be normal, and there is no uniform bound on the dimensions in this statement.
-- source:
--   Trace class groups, arXiv:1501.02375v5, PDF p. 13, Examples 3.2, second bullet

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P60

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P60

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

/-- Examples 3.2, second bullet, PDF p.13: a locally compact group with a
closed abelian subgroup of finite index has only finite-dimensional irreducible
unitary representations. The supplied subgroup need not be normal. -/
theorem closed_finiteIndex_abelian_finiteRepresentationType
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (A : Subgroup G) [A.FiniteIndex]
    (hclosed : IsClosed (A : Set G)) (habelian : ∀ a b : A, a * b = b * a)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : ContinuousUnitaryRepresentation G H) (hpi : IsTopologicallyIrreducible pi) :
    FiniteDimensional ℂ H := by sorry

end QAlgorithms.Papers.Independent.Intake100.P60

end
