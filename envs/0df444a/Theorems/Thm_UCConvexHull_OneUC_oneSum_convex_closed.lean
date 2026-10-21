-- Prove2me | Theorems.Thm_UCConvexHull_OneUC_oneSum_convex_closed
-- name    : UCConvexHull.OneUC.oneSum_convex_closed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:52.510294+00:00
-- url     : https://prove2.me/theorems/ed85c2c6-2816-4f2e-80c4-54647539f9f7
-- title:
--   Remark after Definition 1, p. 17 — the 1-sum composition S¹ ⊕ S² preserves convexity and closedness
-- statement:
--   Let $S^1\subseteq\mathbb R^{n_1}\times\mathbb R$ and $S^2\subseteq\mathbb R^{n_2}\times\mathbb R$, and let
--
--   $$S^1\oplus S^2=\{\,(x^1,x^2,y) : (x^1,y)\in S^1,\ (x^2,y)\in S^2\,\}$$
--
--   be their 1-sum composition (Definition 1). Then:
--   1. if $S^1$ and $S^2$ are convex, so is $S^1\oplus S^2$;
--   2. if $S^1$ and $S^2$ are closed, so is $S^1\oplus S^2$.
--
--   Both facts are needed whenever 1-sums of closed convex hull descriptions are composed, as in Lemma 1 and Theorem 1.
-- source:
--   Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, New MINLP Formulations for the Unit Commitment Problems with Ramping Constraints, manuscript submitted to Operations Research (PDF sha256 eee1c5a4…e224), p. 17, remark after Definition 1

import Mathlib
import Definitions.Def_UCConvexHull_OneUC_HullTools

namespace UCConvexHull.OneUC

/-- Remark after Definition 1 (p. 17): the 1-sum composition preserves convexity and closedness. -/
theorem oneSum_convex_closed {n₁ n₂ : ℕ} (S₁ : Set ((Fin n₁ → ℝ) × ℝ))
    (S₂ : Set ((Fin n₂ → ℝ) × ℝ)) :
    (Convex ℝ S₁ → Convex ℝ S₂ → Convex ℝ (oneSum S₁ S₂)) ∧
      (IsClosed S₁ → IsClosed S₂ → IsClosed (oneSum S₁ S₂)) := by sorry

end UCConvexHull.OneUC
