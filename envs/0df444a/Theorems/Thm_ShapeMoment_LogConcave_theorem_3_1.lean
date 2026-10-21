-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_theorem_3_1
-- name    : ShapeMoment.LogConcave.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:12.888474+00:00
-- url     : https://prove2.me/theorems/3ed6bf91-d8f0-4ee8-ace5-253bf3e14277
-- title:
--   Theorem 3.1 — extreme-point minimum on a compact set
-- statement:
--   Let $S\subseteq\mathbb R^n$ be nonempty and compact, without assuming convexity, and let $c$ be lower semicontinuous and quasiconcave. Then
--
--   $$\exists x\in\operatorname{ext}S:\quad c(x)=\min_{y\in S}c(y).$$
--
--   This provides an optimal extreme point for the compact primed moment problem.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 8, Theorem 3.1, with standing hypotheses of (6)

import Mathlib

namespace ShapeMoment.LogConcave

theorem theorem_3_1 (n : ℕ) (S : Set (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    (hne : S.Nonempty) (hcompact : IsCompact S)
    (hlsc : LowerSemicontinuous c) (hqc : QuasiconcaveOn ℝ Set.univ c) :
    ∃ x ∈ S.extremePoints ℝ, IsMinOn c S x := by sorry

end ShapeMoment.LogConcave
