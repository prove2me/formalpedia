-- Prove2me | Theorems.Thm_SignRankMargin_OREquality_lemma_11
-- name    : SignRankMargin.OREquality.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:42:45.696801+00:00
-- url     : https://prove2.me/theorems/4300e883-e324-4e70-b221-6ff235ac5108
-- title:
--   Lemma 11 — isotropic realization
-- statement:
--   Let $F$ be a Boolean matrix on finite nonempty sets $X,Y$, and suppose $\operatorname{signRank}(F)=r$. There exist unit vectors $u_x,v_y\in\mathbb R^r$ strictly realizing $F$ such that
--
--   $$
--   \frac{1}{|X||Y|}\sum_{x\in X}\sum_{y\in Y}|\langle u_x,v_y\rangle|^2=\frac1r.
--   $$
--
--   Both vector families are produced in the minimum sign-rank dimension, and every vector has norm exactly one. The conclusion is exact equality, with no approximation or general-position hypothesis. This is the geometric normalization used by the spectral witness result.
--
--   **Formalization Note** On nonempty row and column sets, strict realization forces positive sign-rank, so $1/r$ does not use the division-by-zero convention.
--
--   Differences from the source:
--   - encoding: finite nonempty row and column sets and uniform pair average → Fintype and Nonempty instances; explicit double sum divided by the product of cardinalities; reason: represents exactly the finite uniform average and its positive denominators
-- source:
--   Gabriel Hart, Kaave Hosseini, STOC 2027 submission #728 (October 2026), Lemma 11 (attributed to Barthe 1998 and Forster 2002), p. 11

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_Geometry

namespace SignRankMargin.OREquality

/-- Lemma 11, p.11: exact average 1/r in the minimum sign-rank dimension. -/
theorem lemma_11 {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : Matrix X Y Bool) (r : ℕ) (hr : signRank F = r) :
    ∃ (u : X → EuclideanSpace ℝ (Fin r)) (v : Y → EuclideanSpace ℝ (Fin r)),
      UnitRealization F r u v ∧
      uniformAverage (fun x y => |inner ℝ (u x) (v y)| ^ 2) = 1 / (r : ℝ) := by sorry

end SignRankMargin.OREquality
