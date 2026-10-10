-- Prove2me | Theorems.Thm_StrictCQ_AGP_proposition_3_1
-- name    : StrictCQ.AGP.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:27.362776+00:00
-- url     : https://prove2.me/theorems/bbce815a-b704-43e0-b7b6-53d21a519f8f
-- title:
--   Proposition 3.1, p. 5 — for nonempty closed convex C and x ∈ C, ω ∈ N_C(x) iff P_C(x + ω) = x
-- statement:
--   Let $C\subset\mathbb R^n$ be a nonempty, closed, convex set and $x\in C$. For every $\omega\in\mathbb R^n$,
--
--   $$
--   \omega\in N_C(x)\iff P_C(x+\omega)=x,
--   $$
--
--   where $N_C(x)$ is the normal cone of convex analysis and $P_C$ is the Euclidean projection onto $C$.
--
--   This is the bridge between projections and normal cones used twice in the proof of Theorem 4.2: to turn the projection residual of AGP into a normal vector, and conversely to turn normal vectors into projections.
--
--   **Formalization Note** $P_C(x+\omega)=x$ is stated as "$x$ is a Euclidean projection of $x+\omega$ onto $C$", i.e. $x\in C$ and $\|x+\omega-x\|\le\|x+\omega-w\|$ for all $w\in C$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 5, Proposition 3.1 (citing Rockafellar–Wets, Proposition 6.17)

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

/-- Proposition 3.1: for a nonempty closed convex `S` and `x ∈ S`, `w ∈ N_S(x)` iff
`P_S(x + w) = x`. -/
theorem proposition_3_1 {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (hne : S.Nonempty)
    (hcl : IsClosed S) (hcv : Convex ℝ S) (x w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) :
    w ∈ normalCone S x ↔ IsProj S (x + w) x := by sorry

end StrictCQ.AGP
