-- Prove2me | Theorems.Thm_RelaxationMethod_ConvexDomain_limit_mem_frontier
-- name    : RelaxationMethod.ConvexDomain.limit_mem_frontier
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:51:18.542611+00:00
-- url     : https://prove2.me/theorems/d380766e-8f8e-441f-8975-0bcd9ed66f3e
-- title:
--   §10 — the limit of an infinite reflexion sequence lies on the boundary of $A$
-- statement:
--   Let $A \subseteq E_n$ be a nonempty closed bounded convex set and let $\{p_\nu\}$ be a run of the reflexion process (3.1), (3.2) with $p_\nu \notin A$ for all $\nu$. If $p_\nu \to a$, then
--   $$a \in A \quad\text{and}\quad a \in \partial A.$$
--
--   The paper derives this "by the argument of §5": the distance from $p_\nu$ to $A$ equals $\tfrac12|p_{\nu+1} - p_\nu|$, which tends to $0$.
--
--   **Formalization Note** "Boundary" is the topological boundary `frontier A`. No dimension hypothesis is needed for this step.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 403, §10, proof of Theorem 3, Case 1 (citing §5, p. 399)

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
open Filter Topology

namespace RelaxationMethod.ConvexDomain

/-- §10, p. 403 (by the argument of §5, p. 399): if the reflexion process with respect to a
closed bounded convex set `A` produces an infinite sequence converging to `a`, then `a ∈ A` and
`a` lies on the boundary of `A`. -/
theorem limit_mem_frontier {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsImageRun A p) (hinf : ∀ ν : ℕ, p ν ∉ A)
    (a : EuclideanSpace ℝ (Fin n)) (ha : Tendsto p atTop (𝓝 a)) :
    a ∈ A ∧ a ∈ frontier A := by sorry

end RelaxationMethod.ConvexDomain
