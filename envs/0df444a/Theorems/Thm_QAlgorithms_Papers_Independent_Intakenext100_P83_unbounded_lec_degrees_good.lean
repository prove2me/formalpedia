-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P83_unbounded_lec_degrees_good
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P83.unbounded_lec_degrees_good
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:10:03.18047+00:00
-- url     : https://prove2.me/theorems/68a6405c-67be-473f-905e-7a990ce833d4
-- title:
--   Unbounded LEC degrees imply goodness
-- statement:
--   Let $Z_\bullet$ be a simplicial topological space. Suppose that locally equiconnected degrees occur arbitrarily far out:
--
--   $$
--   \forall N\in\mathbb N\;\exists q\ge N:\ Z_q\text{ is locally equiconnected}.
--   $$
--
--   Then $Z_\bullet$ is good: every degeneracy $s_i:Z_n\to Z_{n+1}$ is a closed cofibration, for every $n\ge0$ and $0\le i\le n$. Here locally equiconnected means that the diagonal is a closed cofibration. This supplies a criterion for goodness from the topology of the individual degrees.
-- source:
--   Two-Categorical Bundles and Their Classifying Spaces, arXiv:math/0612549v2, PDF p. 21, Corollary 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P83

open CategoryTheory

open scoped Simplicial

namespace QAlgorithms.Papers.Independent.Intakenext100.P83

universe u v

/-- Corollary 5.2, PDF p. 21. Infinitely many LEC degrees are expressed as
an unbounded set of natural degrees, not as one LEC degree. -/
theorem unbounded_lec_degrees_good (Z : SimplicialObject TopCat.{u})
    (h : ∀ N : ℕ, ∃ q : ℕ, N ≤ q ∧ IsLocallyEquiconnected (Z _⦋q⦌)) :
    IsGood Z := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P83
