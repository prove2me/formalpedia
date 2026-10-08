-- Prove2me | Theorems.Thm_RobustUncLP_WorstCase_proposition_2_1_i
-- name    : RobustUncLP.WorstCase.proposition_2_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T05:52:26.350981+00:00
-- url     : https://prove2.me/theorems/03ef4a1f-25e7-4e99-aecd-06d1afcc43cb
-- title:
--   Proposition 2.1(i), p. 5 — under constraint-wise uncertainty and boundedness, (P_𝒰) is infeasible iff some instance is
-- statement:
--   Let $\mathcal U$ be a nonempty, convex and closed set of real $m\times n$ matrices and $f\in\mathbb R^n$. Assume the uncertainty is constraint-wise, $\mathcal U = \mathcal U_1\times\dots\times\mathcal U_m$, and the Boundedness Assumption holds: some convex compact $Q\subseteq\mathbb R^n$ contains the feasible set of every instance. Then
--   $$G_{\mathcal U} = \emptyset \iff \exists A \in \mathcal U:\ \{x \mid Ax\ge0,\ f^{T}x = 1\} = \emptyset,$$
--   that is, the robust counterpart $(P_{\mathcal U})$ is infeasible if and only if there exists an infeasible instance.
--
--   Part (ii) of Proposition 2.1 is derived from this statement applied to an augmented uncertain program, so it is stated for every $m$, $\mathcal U$ and $f$.
--
--   **Formalization Note** Convexity and closedness of $\mathcal U$ are the standing assumption of §2.1. Nonemptiness of $\mathcal U$ is added: the paper takes a nonempty family of instances for granted, and for $\mathcal U = \emptyset$, $f = 0$ the robust counterpart is infeasible while no instance exists.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 5, Proposition 2.1(i); standing assumption §2.1, p. 3

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting
open Matrix

namespace RobustUncLP.WorstCase

theorem proposition_2_1_i {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (f : Fin n → ℝ)
    (hconv : Convex ℝ U) (hclosed : IsClosed U) (hne : U.Nonempty)
    (hcw : IsConstraintWise U) (hbdd : BoundednessAssumption U f) :
    robustFeas U f = ∅ ↔ ∃ A ∈ U, instFeas f A = ∅ := by sorry

end RobustUncLP.WorstCase
