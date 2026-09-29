-- Prove2me | Theorems.Thm_RelaxationMethod_ConvexDomain_fejerMonotone_of_infinite_run
-- name    : RelaxationMethod.ConvexDomain.fejerMonotone_of_infinite_run
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:49:08.511994+00:00
-- url     : https://prove2.me/theorems/f15aaa48-e368-4e0a-bc5c-e9314fa35049
-- title:
--   §10 — an infinite reflexion sequence is Fejér-monotone
-- statement:
--   Let $A \subseteq E_n$ be a nonempty closed bounded convex set and let $p_0, p_1, \dots$ be a run of the reflexion process (3.1), (3.2) with respect to $A$ that never enters $A$ ($p_\nu \notin A$ for all $\nu$). Then $\{p_\nu\}$ is Fejér-monotone with respect to $A$:
--   $$p_\nu \ne p_{\nu+1}, \qquad |p_{\nu+1} - a| \le |p_\nu - a| \quad (a \in A,\ \nu = 0, 1, \dots).$$
--
--   This is the first step of the proof of Theorem 3, Case 1: it makes the convergence Lemma 1 applicable.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 403, §10, proof of Theorem 3, Case 1

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
import Definitions.Def_RelaxationMethod_Shared_FejerMonotone

namespace RelaxationMethod.ConvexDomain

/-- §10, p. 403: an infinite sequence produced by the reflexion process (3.1), (3.2) with respect
to a closed bounded convex set `A` is Fejér-monotone with respect to `A`. -/
theorem fejerMonotone_of_infinite_run {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsImageRun A p) (hinf : ∀ ν : ℕ, p ν ∉ A) :
    RelaxationMethod.Shared.IsFejerMonotone A p := by sorry

end RelaxationMethod.ConvexDomain
