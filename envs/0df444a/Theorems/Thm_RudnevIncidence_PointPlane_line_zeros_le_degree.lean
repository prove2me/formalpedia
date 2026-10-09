-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_line_zeros_le_degree
-- name    : RudnevIncidence.PointPlane.line_zeros_le_degree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:11.576612+00:00
-- url     : https://prove2.me/theorems/73980e28-921f-4c79-a199-818c4a6dba8e
-- title:
--   §5, p. 16 — a line not contained in Z(Q) meets Z(Q) in at most d = deg Q points
-- statement:
--   Let $Q\in\mathbb F[x_0,x_1,x_2,x_3]$ be homogeneous of degree $d$, and let $l$ be a line of $\mathbb P^3$ not contained in the zero set $Z(Q)$. Then $l$ meets $Z(Q)$ in at most $d$ points: any finite set $S$ of points of $l$ at which $Q$ vanishes has $|S|\le d$.
--
--   Equivalently, a line carrying more than $d$ zeros of $Q$ is contained in $Z(Q)$. The proof of Theorem 12 uses both readings: the popular lines of $L'_\alpha$ lie in $Z(Q)$, and every line of $L_\beta$ outside $Z(Q)$ meets it at most $d$ times.
--
--   **Formalization Note** The line is a 2-dimensional subspace $W$ of $\mathbb F^4$; "not contained in $Z(Q)$" is the existence of a vector of $W$ at which $Q$ does not vanish. Holds over every field.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, p. 16, §5, "It follows that all the lines in L̄′α are contained in Z̄ … at most d times"

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem line_zeros_le_degree {F : Type*} [Field F] (Q : MvPolynomial (Fin 4) F) (d : ℕ)
    (hQ : Q.IsHomogeneous d) (W : Submodule F (Fin 4 → F)) (hW : Module.finrank F W = 2)
    (hnot : ∃ w ∈ W, MvPolynomial.eval w Q ≠ 0) (S : Finset (ℙ F (Fin 4 → F)))
    (hS : ∀ x ∈ S, x.rep ∈ W ∧ MvPolynomial.eval x.rep Q = 0) :
    S.card ≤ d := by sorry
end RudnevIncidence.PointPlane
