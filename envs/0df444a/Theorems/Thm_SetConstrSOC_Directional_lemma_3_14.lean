-- Prove2me | Theorems.Thm_SetConstrSOC_Directional_lemma_3_14
-- name    : SetConstrSOC.Directional.lemma_3_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:12.954055+00:00
-- url     : https://prove2.me/theorems/bb82c310-a272-431d-9aae-f9891d1b4337
-- title:
--   Lemma 3, (14) — normals of the second-order tangent set
-- statement:
--   Let $S\subseteq\mathbb R^n$ be closed, $x\in S$, $d\in T_S(x)$, and $w\in T_S^2(x;d)$. Then
--
--   $$
--   N_{T_S^2(x;d)}(w)\subseteq N_S(x;d).
--   $$
--
--   The normal on the left is the limiting normal cone to the second-order tangent set, and the normal on the right is the directional limiting normal cone to the original set. The inclusion connects multipliers of the second-order linearized problem to directional multipliers of (P).
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, p. 12, Lemma 3, (14)

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

namespace SetConstrSOC.Directional

/-- Lemma 3, (14), p. 12: normals to the second-order tangent set are directional normals. -/
theorem lemma_3_14 {n : ℕ} (S : Set (E n)) (hS : IsClosed S)
    (x d w : E n) (hx : x ∈ S) (hd : d ∈ tangentCone S x)
    (hw : w ∈ secondOrderTangentSet S x d) :
    limNormal (secondOrderTangentSet S x d) w ⊆ dirLimNormal S x d := by sorry

end SetConstrSOC.Directional
