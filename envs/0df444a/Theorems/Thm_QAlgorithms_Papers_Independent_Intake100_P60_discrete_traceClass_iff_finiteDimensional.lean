-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P60_discrete_traceClass_iff_finiteDimensional
-- name    : QAlgorithms.Papers.Independent.Intake100.P60.discrete_traceClass_iff_finiteDimensional
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:07:25.720508+00:00
-- url     : https://prove2.me/theorems/f8b688be-4d36-4f6c-a951-cd29c870b5f0
-- title:
--   Discrete trace-class representations are exactly the finite-dimensional ones
-- statement:
--   Let $\Gamma$ be a discrete Hausdorff locally compact group and let $\pi$ be a strongly continuous unitary representation on an arbitrary complete complex Hilbert space $H$. Fix counting Haar measure. For a finitely supported complex function $f$ on $\Gamma$, let $\pi(f)=\sum_{g\in\Gamma}f(g)\pi(g)$. Then
--
--   $$
--   \bigl[\pi(f)\text{ is trace class for every finitely supported }f\bigr]
--   \quad\Longleftrightarrow\quad
--   \dim_{\mathbb C}H<\infty.
--   $$
--
--   Here trace class has its usual infinite-dimensional operator meaning. No irreducibility or nonzero-space assumption is imposed. This identifies the trace-class representation property for discrete groups. Positive rescaling of Haar measure leaves the equivalence unchanged.
-- source:
--   Trace class groups, arXiv:1501.02375v5, PDF p. 5, Examples 1.5, second bullet

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P60

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P60

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

/-- Example 1.5, PDF p.5: a representation of a discrete group is trace class
if and only if its Hilbert space is finite-dimensional. Irreducibility is not
assumed, and the zero Hilbert space is included. -/
theorem discrete_traceClass_iff_finiteDimensional
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [DiscreteTopology G]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : ContinuousUnitaryRepresentation G H) :
    DiscreteTraceClass pi ↔ FiniteDimensional ℂ H := by sorry

end QAlgorithms.Papers.Independent.Intake100.P60

end
