-- Prove2me | Theorems.Thm_RelaxationMethod_ConvexDomain_theorem3
-- name    : RelaxationMethod.ConvexDomain.theorem3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:53:40.473983+00:00
-- url     : https://prove2.me/theorems/704cb55c-7438-44c7-8a79-8ad419a50972
-- title:
--   Theorem 3 — reflexion in a closed bounded convex set terminates or ends in oscillation
-- statement:
--   Let $A \subseteq E_n$ be a nonempty closed bounded convex set of dimension $r$, and let $L_r$ be the $r$-flat containing $A$ (its affine span). Let $p_0 \notin A$ and let $\{p_\nu\}$ be a sequence obtained by the reflexion process
--   $$p_{\nu+1} = F(p_\nu) = p_\nu + 2(q_\nu - p_\nu), \qquad q_\nu \text{ the point of } A \text{ nearest to } p_\nu \quad (p_\nu \notin A).$$
--
--   1. **Case 1.** If $r = n$, the process always terminates: $p_N \in A$ for some $N$.
--   2. **Case 2.** Let $r < n$. If $p_0 \in L_r$, the process terminates. If $p_0 \notin L_r$, the process produces an infinite sequence ($p_\nu \notin A$ for all $\nu$), and there are a number $\nu_0$ and two distinct points $u \ne v$, symmetric with respect to $L_r$, such that for all $\nu > \nu_0$ the points $p_\nu$ oscillate between them:
--   $$\{p_\nu, p_{\nu+1}\} = \{u, v\} \text{ with } p_\nu \ne p_{\nu+1} \qquad (\nu > \nu_0).$$
--
--   This extends the finite termination of the reflexion method for full-dimensional polytopes (Theorem 1, Case 2) to the infinite family of all supporting half-spaces of a convex body.
--
--   **Formalization Note** $r = n$ is `affineSpan ℝ A = ⊤` and $r < n$ is `affineSpan ℝ A ≠ ⊤`. The statement holds for **every** run from **every** $p_0 \notin A$. "Symmetric with respect to $L_r$" means the midpoint of $u, v$ lies in $L_r$ and $u - v$ is orthogonal to $L_r$. Nonemptiness of $A$ is implicit in the paper ("of dimension $r$", "the point of $A$ nearest to $p$").
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 402, Theorem 3, Cases 1 and 2

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
import Definitions.Def_RelaxationMethod_ConvexDomain_SymmetricWrt

namespace RelaxationMethod.ConvexDomain

/-- Theorem 3, p. 402. Let `A ⊆ E_n` be a nonempty closed bounded convex set with affine span
`L_r = affineSpan ℝ A`, and let `p₀ ∉ A` start a run of the reflexion process (3.1), (3.2).
Case 1: if `L_r` is the whole space (`r = n`), the process terminates.
Case 2: if `L_r ≠ ⊤` (`r < n`): if `p₀ ∈ L_r` the process terminates; if `p₀ ∉ L_r` the process
never enters `A` and, for all `ν > ν₀`, `p_ν` alternates between two distinct points `u`, `v`
symmetric with respect to `L_r`. -/
theorem theorem3 {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (h0 : p 0 ∉ A) (hrun : IsImageRun A p) :
    (affineSpan ℝ A = ⊤ → ∃ N : ℕ, p N ∈ A) ∧
    (affineSpan ℝ A ≠ ⊤ →
      (p 0 ∈ affineSpan ℝ A → ∃ N : ℕ, p N ∈ A) ∧
      (p 0 ∉ affineSpan ℝ A →
        (∀ ν : ℕ, p ν ∉ A) ∧
        ∃ ν₀ : ℕ, ∃ u v : EuclideanSpace ℝ (Fin n), u ≠ v ∧
          IsSymmetricWrt (affineSpan ℝ A) u v ∧
          ∀ ν : ℕ, ν > ν₀ →
            (p ν = u ∧ p (ν + 1) = v) ∨ (p ν = v ∧ p (ν + 1) = u))) := by sorry

end RelaxationMethod.ConvexDomain
