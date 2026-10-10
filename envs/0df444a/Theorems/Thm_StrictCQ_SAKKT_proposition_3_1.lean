-- Prove2me | Theorems.Thm_StrictCQ_SAKKT_proposition_3_1
-- name    : StrictCQ.SAKKT.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:03.306482+00:00
-- url     : https://prove2.me/theorems/7ee74c23-d51a-4f34-ad2e-c53a5b7df074
-- title:
--   Proposition 3.1, p. 5 — for nonempty closed convex C and x ∈ C, ω ∈ N_C(x) iff P_C(x + ω) = x
-- statement:
--   Let $C\subseteq\mathbb R^n$ be a nonempty, closed, convex set and let $x\in C$. For every $\omega\in\mathbb R^n$,
--   $$\omega\in N_C(x)\iff P_C(x+\omega)=x,$$
--   where $N_C(x)=\{w:\langle w,z-x\rangle\le0\ \forall z\in C\}$ is the normal cone of convex analysis and $P_C$ is the Euclidean projection onto $C$.
--
--   This is the link between normal cones and projections ([Rockafellar–Wets, Proposition 6.17]) through which the AGP condition is turned into a statement about normal cones.
--
--   **Formalization Note** "$P_C(x+\omega)=x$" is stated as "$x$ is a Euclidean projection of $x+\omega$ onto $C$" ($x\in C$ and $\|x+\omega-x\|\le\|x+\omega-z\|$ for all $z\in C$), which is equivalent because the projection onto a nonempty closed convex set is unique.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 5, Proposition 3.1

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

/-- Proposition 3.1: for a nonempty closed convex `S` and `x ∈ S`, `w ∈ N_S(x)` iff
`P_S(x + w) = x`. -/
theorem proposition_3_1 {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (hne : S.Nonempty)
    (hcl : IsClosed S) (hcv : Convex ℝ S) (x w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) :
    w ∈ StrictCQ.AGP.normalCone S x ↔ StrictCQ.AGP.IsProj S (x + w) x := by sorry

end StrictCQ.SAKKT
