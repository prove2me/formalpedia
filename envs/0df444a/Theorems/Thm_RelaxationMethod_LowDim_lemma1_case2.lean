-- Prove2me | Theorems.Thm_RelaxationMethod_LowDim_lemma1_case2
-- name    : RelaxationMethod.LowDim.lemma1_case2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:30:16.57593+00:00
-- url     : https://prove2.me/theorems/8c581a0a-8984-4969-8fe9-57e0beb01f9a
-- title:
--   Lemma 1, Case 2 — a Fejér-monotone sequence converges or its limit points lie on a sphere with axis $L_r$
-- statement:
--   Let $A \subseteq E_n$ be nonempty, let $L_r$ be the affine span of $A$, and assume $L_r \neq E_n$ (that is, $r < n$). Let $\{q_\nu\}$ be Fejér-monotone with respect to $A$. Then either $\{q_\nu\}$ converges to a point, or there is a point $c \notin L_r$ such that every limit point of $\{q_\nu\}$ lies on the spherical surface having $L_r$ as its axis and passing through $c$:
--   $$\text{every limit point } x \text{ satisfies } |x - a| = |c - a| \text{ for all } a \in L_r.$$
--
--   Together with Case 1 ($r = n$: convergence), this is the paper's Lemma 1. Case 2 is what makes a non-convergent run accumulate on a sphere around the axis $L_r$, the starting point of both cases of Theorem 2.
--
--   **Formalization Note** The paper states the lemma for the polytope $A$; it is stated here for an arbitrary nonempty set $A$, which is stronger (the proof on p. 398 uses only that $A$ spans $L_r$, and §10 applies it to a convex set). "Limit point of the sequence" is a cluster point (`MapClusterPt x atTop q`), not a point of the closure of the range. The condition $c \notin L_r$ excludes the degenerate one-point locus.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, p. 397, §4, Lemma 1, Case 2 (proof p. 398)

import Mathlib
import Definitions.Def_RelaxationMethod_Shared_FejerMonotone
import Definitions.Def_RelaxationMethod_LowDim_AxisSphere

open Filter Topology

namespace RelaxationMethod.LowDim

/-- Lemma 1, Case 2, p. 397: if `A` is nonempty and its affine span `L_r` is not the whole space
(`r < n`), a Fejér-monotone sequence with respect to `A` either converges or all its limit
points lie on one spherical surface having `L_r` as its axis. Stated for an arbitrary nonempty
set `A` (the paper states it for the polytope `A`). -/
theorem lemma1_case2 {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) (hA : A.Nonempty)
    (hr : affineSpan ℝ A ≠ ⊤) (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hq : RelaxationMethod.Shared.IsFejerMonotone A q) :
    (∃ l, Tendsto q atTop (𝓝 l)) ∨
      ∃ c ∉ affineSpan ℝ A,
        ∀ x, MapClusterPt x atTop q → x ∈ axisSphere (affineSpan ℝ A) c := by sorry

end RelaxationMethod.LowDim
