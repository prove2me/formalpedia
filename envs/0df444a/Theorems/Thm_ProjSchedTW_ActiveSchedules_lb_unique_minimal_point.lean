-- Prove2me | Theorems.Thm_ProjSchedTW_ActiveSchedules_lb_unique_minimal_point
-- name    : ProjSchedTW.ActiveSchedules.lb_unique_minimal_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T15:51:45.781542+00:00
-- url     : https://prove2.me/theorems/f3dd3e5a-0b2b-4c73-9f02-3b19d0702b0d
-- title:
--   Lemma 2.4.7 — the lower bound of a nonempty order polyhedron is its unique minimal point
-- statement:
--   Let $O$ be a strict order in the activity set $V$ and let $\mathcal S_T(O)$ be its order polyhedron, the set of time-feasible schedules $S$ with $S_j\ge S_i+p_i$ for all $(i,j)\in O$. Assume $\mathcal S_T(O)\neq\emptyset$. Write
--   $$lb\,\mathcal S_T(O)=\Bigl(\min_{S\in\mathcal S_T(O)}S_0,\ \dots,\ \min_{S\in\mathcal S_T(O)}S_{n+1}\Bigr)$$
--   for the vector of componentwise minima. Then $lb\,\mathcal S_T(O)$ is a minimal point of $\mathcal S_T(O)$ — it lies in $\mathcal S_T(O)$ and no other point $S'\in\mathcal S_T(O)$ satisfies $S'\le lb\,\mathcal S_T(O)$ — and it is the only minimal point of $\mathcal S_T(O)$.
--
--   The minimal point $\min\mathcal S_T(O)$ is the earliest schedule of the order network $N(O)$; it is the schedule computed at every node of the branch-and-bound methods of §2.5, and it is the object parts (c) and (d) of Theorem 2.4.9 refer to.
--
--   **Formalization Note** The book states the lemma for any strict order; the nonemptiness of $\mathcal S_T(O)$ (time-feasibility of $O$) is added, since the lower bound of an empty set is not a point of it. The componentwise minima are real infima (`sInf`).
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 43, Lemma 2.4.7

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project

namespace ProjSchedTW.ActiveSchedules

/-- Lemma 2.4.7 (p. 43): for a strict order `O` in `V` whose order polyhedron `S_T(O)` is
nonempty, the vector `lb S_T(O)` of componentwise infima is the unique minimal point of
`S_T(O)`. -/
theorem lb_unique_minimal_point {n : ℕ} {K : Type} (P : Project n K)
    (O : Set (Fin (n + 2) × Fin (n + 2))) (hO : IsStrictOrderRel O)
    (hne : (orderPolyhedron P O).Nonempty) :
    Minimal (· ∈ orderPolyhedron P O) (lowerBound (orderPolyhedron P O)) ∧
      ∀ S : Fin (n + 2) → ℝ, Minimal (· ∈ orderPolyhedron P O) S →
        S = lowerBound (orderPolyhedron P O) := by sorry

end ProjSchedTW.ActiveSchedules
