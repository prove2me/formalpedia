-- Prove2me | Theorems.Thm_TopCover_finite_components_of_finite_cover
-- name    : TopCover.finite_components_of_finite_cover
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T07:24:41.545854+00:00
-- url     : https://prove2.me/theorems/ffee277c-2b8d-4ca8-9f6c-2aaa8d12f022
-- title:
--   A set covered by finitely many connected subsets has finitely many components
-- statement:
--   Let $U$ be a subset of a topological space, and suppose $U$ is covered by a family $(V_i)_{i \in \iota}$ indexed by a **finite** type, where each $V_i$ is preconnected and contained in $U$. Then $U$ has only finitely many connected components: the set
--
--   $$\{\, C : \exists\, x \in U,\ C = \mathrm{connectedComponentIn}\ U\ x \,\}$$
--
--   is finite.
--
--   **Role.** The counting step one wants whenever a set is built from finitely many pieces — a finite union of intervals in $\mathbb{R}$, a finite union of cells, the moved set of a piecewise-defined map. It converts a decomposition into a bound on the number of components without any metric, separation, or local-connectedness assumption, and without requiring the pieces to be open, disjoint, or nonempty.
--
--   The mechanism is that the component set is the image of the index type: each component contains some $V_i$ entirely — any $V_i$ meeting it, since $V_i$ is preconnected and inside $U$, so lies in that component — and every point of $U$ lies in some $V_i$. Sending $i$ to the component of a chosen point of $V_i$ therefore hits every component, so the component set is a subset of the range of a function on a finite type.
--
--   **Formalization note.** `IsPreconnected` rather than `IsConnected` is deliberate: it permits empty pieces, so a decomposition need not be pruned before use. No separation axiom is assumed.
-- source:
--   Standard point-set topology; this is the finite-cover counting argument for connected components, and no single canonical reference states it in this form. Compare Bourbaki, General Topology I, Chapter I, Section 11 (connected components) and Munkres, Topology 2nd ed., Section 25, where the ingredients appear -- a connected subset meeting a component lies in it, and components partition the set -- but the finite-cover corollary is left to the reader. PROVENANCE: extracted while formalizing M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, where it is the counting step behind the Section 2 fact (p. 488) that a PLF support has finitely many components.

import Mathlib

namespace TopCover

theorem finite_components_of_finite_cover {α : Type*} [TopologicalSpace α] {U : Set α}
    {ι : Type*} [Finite ι] (V : ι → Set α)
    (hconn : ∀ i, IsPreconnected (V i)) (hsub : ∀ i, V i ⊆ U) (hcov : U ⊆ ⋃ i, V i) :
    {C : Set α | ∃ x ∈ U, C = connectedComponentIn U x}.Finite := by
  sorry

end TopCover
