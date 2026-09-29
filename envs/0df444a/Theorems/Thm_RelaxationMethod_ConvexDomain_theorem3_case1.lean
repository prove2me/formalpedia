-- Prove2me | Theorems.Thm_RelaxationMethod_ConvexDomain_theorem3_case1
-- name    : RelaxationMethod.ConvexDomain.theorem3_case1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:51:48.212579+00:00
-- url     : https://prove2.me/theorems/24e83455-024b-4803-8368-4f153ca12380
-- title:
--   Theorem 3, Case 1 — reflexion in a full-dimensional convex body always terminates
-- statement:
--   Let $A \subseteq E_n$ be a nonempty closed bounded convex set of dimension $n$ (its affine span is $E_n$). For every starting point $p_0 \notin A$, every run $p_0, p_1, \dots$ of the reflexion process
--   $$p_{\nu+1} = p_\nu + 2(q_\nu - p_\nu), \qquad q_\nu = \text{the point of } A \text{ nearest to } p_\nu,$$
--   terminates: there is an $N$ with $p_N \in A$.
--
--   This is Case 1 of Theorem 3, stated separately because the paper's proof of Case 2 reduces to it.
--
--   **Formalization Note** "Dimension $n$" is `affineSpan ℝ A = ⊤`; nonemptiness of $A$ is implicit in the paper.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 402, Theorem 3, Case 1

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess

namespace RelaxationMethod.ConvexDomain

/-- Theorem 3, Case 1, p. 402: if the closed bounded convex set `A ⊆ E_n` has dimension `n`
(its affine span is the whole space), then for every starting point `p₀ ∉ A` the reflexion
process (3.1), (3.2) terminates: some `p_N` lies in `A`. -/
theorem theorem3_case1 {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A) (hspan : affineSpan ℝ A = ⊤)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (h0 : p 0 ∉ A) (hrun : IsImageRun A p) :
    ∃ N : ℕ, p N ∈ A := by sorry

end RelaxationMethod.ConvexDomain
