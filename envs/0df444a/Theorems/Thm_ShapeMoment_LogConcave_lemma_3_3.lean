-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_lemma_3_3
-- name    : ShapeMoment.LogConcave.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:12.659021+00:00
-- url     : https://prove2.me/theorems/12025ba8-1c6e-4989-8757-c7eabda9821c
-- title:
--   Lemma 3.3 — compact closed convex hull
-- statement:
--   For a compact set $S\subseteq\mathbb R^n$,
--
--   $$\overline{\operatorname{conv}}S\text{ is compact and convex}.$$
--
--   This supplies a compact convex set for the extreme-point existence argument.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 8, Lemma 3.3

import Mathlib

namespace ShapeMoment.LogConcave

theorem lemma_3_3 (n : ℕ) (S : Set (Fin n → ℝ)) (hS : IsCompact S) :
    IsCompact (closedConvexHull ℝ S) ∧ Convex ℝ (closedConvexHull ℝ S) := by sorry

end ShapeMoment.LogConcave
