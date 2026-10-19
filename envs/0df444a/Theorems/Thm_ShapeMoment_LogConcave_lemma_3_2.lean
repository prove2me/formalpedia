-- Prove2me | Theorems.Thm_ShapeMoment_LogConcave_lemma_3_2
-- name    : ShapeMoment.LogConcave.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:11.699091+00:00
-- url     : https://prove2.me/theorems/249715c4-5e07-4791-8d7c-950bcb8623ec
-- title:
--   Lemma 3.2 — extreme-point minimum on a convex set
-- statement:
--   Let $S\subseteq\mathbb R^n$ be nonempty, compact, and convex, and let $c$ be lower semicontinuous and quasiconcave. Then
--
--   $$\exists x\in\operatorname{ext}S:\quad c(x)=\min_{y\in S}c(y).$$
--
--   The regularity of $c$ and nonemptiness of $S$ are stated in the setup of problem (6) before the lemma.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 8, Lemma 3.2, with standing hypotheses of (6)

import Mathlib

namespace ShapeMoment.LogConcave

theorem lemma_3_2 (n : ℕ) (S : Set (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    (hne : S.Nonempty) (hcompact : IsCompact S) (hconv : Convex ℝ S)
    (hlsc : LowerSemicontinuous c) (hqc : QuasiconcaveOn ℝ Set.univ c) :
    ∃ x ∈ S.extremePoints ℝ, IsMinOn c S x := by sorry

end ShapeMoment.LogConcave
