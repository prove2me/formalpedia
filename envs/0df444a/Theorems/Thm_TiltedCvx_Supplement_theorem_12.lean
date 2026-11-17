-- Prove2me | Theorems.Thm_TiltedCvx_Supplement_theorem_12
-- name    : TiltedCvx.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:31:25.5783+00:00
-- url     : https://prove2.me/theorems/aa8da781-ad28-4158-a3e1-de1475d6e1db
-- title:
--   Theorem 12 — closure of $\mathcal F^\gamma$ under suprema
-- statement:
--   Let $\gamma\in(0,1]$, let $\{f_i\}_{i\in I}\subseteq\mathcal F^\gamma$ be a non-empty family, and suppose that $s:=\sup_{i\in I}f_i$ is proper. Then
--
--   $$
--   s\in\mathcal F^\gamma .
--   $$
--
--   As for convex functions, pointwise suprema stay in the class; the index set is arbitrary (possibly uncountable).
--
--   **Formalization Note** $I$ is an arbitrary non-empty type and $s$ the pointwise supremum in $\overline{\mathbb R}$; $\mathcal F^\gamma$ is the published `classF γ`.
--
--   Differences from the source:
--   - generalization: functions on ℝ^d → functions on a finite-dimensional real inner product space E; reason: every such E is isometric to ℝ^d and ℝ^d = EuclideanSpace ℝ (Fin d) is an instance, so the statement specializes to the paper's
--   - encoding: ℝ̄ = ℝ ∪ {±∞}, dom(f) = {f finite} → EReal and the published TiltedCvx.effDom; reason: Lean convention; same instances
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 12, p.22

import Mathlib
import Definitions.Def_TiltedCvx_IsProper
import Definitions.Def_TiltedCvx_classF

namespace TiltedCvx.Supplement

/-- **Theorem 12 (closure under supremum).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Theorem 12, p.22. Let `γ ∈ (0, 1]`, let `{fᵢ}_{i∈I} ⊆ F^γ` be a non-empty family, and suppose that
`s := sup_{i∈I} fᵢ` is proper. Then `s ∈ F^γ`.

**Formalization Note** The index type `I` is arbitrary (uncountable families allowed) and
non-empty; `s` is the pointwise supremum `⨆ i, fᵢ` in `EReal`. `F^γ` is the published
`classF γ`. -/
theorem theorem_12 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {I : Type*} [Nonempty I]
    (fam : I → E → EReal) (hfam : ∀ i, fam i ∈ (TiltedCvx.classF γ : Set (E → EReal)))
    (hs : TiltedCvx.IsProper (⨆ i, fam i)) :
    (⨆ i, fam i) ∈ (TiltedCvx.classF γ : Set (E → EReal)) := by sorry

end TiltedCvx.Supplement
