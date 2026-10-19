-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P33_closedConvexHullBarycenters
-- name    : QAlgorithms.Papers.Independent.Dependency50.P33.closedConvexHullBarycenters
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:19:59.447596+00:00
-- url     : https://prove2.me/theorems/8bbe05cb-34a1-4170-8a54-013485c68b4f
-- title:
--   Barycenters supported on a closed set give its closed convex hull
-- statement:
--   Let $H$ be a nonzero separable complex Hilbert space. Give its density-operator space $\mathfrak S(H)$ the trace-norm topology and Borel sigma algebra. If $A\subseteq\mathfrak S(H)$ is closed, then for every state $\rho$,
--
--   $$
--   \rho\in\overline{\operatorname{co}}A
--   \quad\Longleftrightarrow\quad
--   \exists\pi\in\mathcal P(A),\qquad \rho=\int_A\sigma\,\pi(d\sigma).
--   $$
--
--   Here $\overline{\operatorname{co}}A$ is the trace-norm closed convex hull, $\mathcal P(A)$ is the set of Borel probability measures on the closed subspace $A$, and the integral is in the trace-class Banach space. Equivalently, these are measures on the state space supported by $A$. No compactness or countability of support is required. The assertion includes $A=\varnothing$, when both sides describe an empty set.
--
--   This is the closed-set barycentric representation used for separability and pure-product representations.
-- source:
--   Separability and Entanglement-Breaking in Infinite Dimensions, arXiv:quant-ph/0504204v1, PDF p. 2, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.RealRegisters (Hilbert)

/-- Lemma 1, PDF p.2: closed convex hull equals barycenters supported on the
closed set. Probability measures on its closed subtype encode precisely this
support condition. The empty closed set is permitted. -/
theorem closedConvexHullBarycenters {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : IsTraceClosed A) (rho : State I) :
    rho.coefficients ∈ traceClosure (convexHull ℝ (State.coefficients '' A)) ↔
      ∃ mu : Measure A, IsProbabilityMeasure mu ∧
        IsBarycenter mu (fun s => s.val.coefficients) rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P33

end
