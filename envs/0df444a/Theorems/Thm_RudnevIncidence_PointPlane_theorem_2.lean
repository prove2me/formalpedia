-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_theorem_2
-- name    : RudnevIncidence.PointPlane.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:53.653157+00:00
-- url     : https://prove2.me/theorems/0283a469-e7e7-4516-b78d-c229585b8ba9
-- title:
--   Theorem 2 (Salmon), p. 3 — an irreducible surface of degree d in P³ containing more than d(11d − 24) lines is ruled (d < p in characteristic p)
-- statement:
--   Let $\mathbb F$ be algebraically closed, and let $Q\in\mathbb F[x_0,x_1,x_2,x_3]$ be an irreducible homogeneous polynomial of degree $d$, defining an irreducible surface $Z(Q)\subset\mathbb P^3$. If $\mathbb F$ has positive characteristic $p$, assume $d<p$. If $Z(Q)$ contains more than
--   $$d(11d-24)$$
--   lines, then $Z(Q)$ is ruled: every point of $Z(Q)$ lies on a line contained in $Z(Q)$.
--
--   The paper cites this result (it is implicit in the proof of Proposition 1 of Voloch's *Surfaces in $\mathbb P^3$ over finite fields*) and invokes it in the proof of Theorem 12 to force a ruled factor of the vanishing polynomial.
--
--   **Formalization Note** "Containing more than $N$ lines" is "contains a finite set of more than $N$ distinct lines", which also covers surfaces with infinitely many lines. The bound $d(11d-24)$ is computed in $\mathbb Z$ because it is negative for $d\le2$. The characteristic constraint is guarded: it applies only when the characteristic is positive. "Ruled" is the incidence-geometric notion of the Setting definition.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, p. 3, Theorem 2 (Salmon); used on p. 16

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem theorem_2 {F : Type*} [Field F] [IsAlgClosed F] (Q : MvPolynomial (Fin 4) F) (d : ℕ)
    (hQ : Irreducible Q) (hd : Q.IsHomogeneous d) (hp : ringChar F ≠ 0 → d < ringChar F)
    (𝓛 : Finset (Submodule F (Fin 4 → F))) (h𝓛 : ∀ W ∈ 𝓛, Module.finrank F W = 2)
    (hZ : ∀ W ∈ 𝓛, ∀ w ∈ W, MvPolynomial.eval w Q = 0)
    (hcard : (d : ℤ) * (11 * (d : ℤ) - 24) < (𝓛.card : ℤ)) :
    IsRuled Q := by sorry
end RudnevIncidence.PointPlane
