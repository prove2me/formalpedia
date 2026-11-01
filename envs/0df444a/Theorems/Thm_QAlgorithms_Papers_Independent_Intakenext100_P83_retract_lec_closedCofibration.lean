-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P83_retract_lec_closedCofibration
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P83.retract_lec_closedCofibration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:09:36.26657+00:00
-- url     : https://prove2.me/theorems/934b5be9-e6ed-449a-a44b-c0b11dcf2dbd
-- title:
--   Retracts of locally equiconnected spaces
-- statement:
--   A topological space is locally equiconnected (LEC) when its diagonal into its square is a closed cofibration. Let $i:A\hookrightarrow X$ be a subspace inclusion, and let $r:X\to A$ be a continuous retraction, so $r\circ i=\mathrm{id}_A$. If $X$ is LEC, then
--
--   $$
--   i\text{ is a closed cofibration},\qquad A\text{ is LEC}.
--   $$
--
--   This preserves both the homotopy extension property of the inclusion and the local equiconnectivity of the retract. The formalization uses the equivalent cylinder-corner retraction definition of a closed cofibration.
-- source:
--   Two-Categorical Bundles and Their Classifying Spaces, arXiv:math/0612549v2, PDF p. 21, Theorem 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P83

open CategoryTheory

open scoped Simplicial

namespace QAlgorithms.Papers.Independent.Intakenext100.P83

universe u v

/-- Theorem 5.1, PDF p. 21. A retract inclusion of a locally equiconnected
space is a closed cofibration, and its domain is locally equiconnected.
`hi` records precisely that the domain has the subspace topology. -/
theorem retract_lec_closedCofibration
    {A : Type u} {X : Type v} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (hi : Topology.IsEmbedding i)
    (r : C(X, A)) (hr : Function.LeftInverse r i)
    (hX : IsLocallyEquiconnected X) :
    IsClosedCofibration i ∧ IsLocallyEquiconnected A := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P83
