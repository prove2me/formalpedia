-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_lemma_3_4
-- name    : ShapeMoment.LogConcave.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:14.104995+00:00
-- url     : https://prove2.me/theorems/d6627416-8629-4487-9ea4-fd0c042e4f8b
-- title:
--   Lemma 3.4 — extreme points of the closed convex hull
-- statement:
--   For compact $S\subseteq\mathbb R^n$,
--
--   $$\operatorname{ext}(\overline{\operatorname{conv}}S)\subseteq\operatorname{ext}S.$$
--
--   This transfers an extreme-point solution from the closed convex hull back to the original set.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 8, Lemma 3.4

import Mathlib

namespace ShapeMoment.LogConcave

theorem lemma_3_4 (n : ℕ) (S : Set (Fin n → ℝ)) (hS : IsCompact S) :
    (closedConvexHull ℝ S).extremePoints ℝ ⊆ S.extremePoints ℝ := by sorry

end ShapeMoment.LogConcave
