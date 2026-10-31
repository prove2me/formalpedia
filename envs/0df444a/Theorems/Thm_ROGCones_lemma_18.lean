-- Prove2me | Theorems.Thm_ROGCones_lemma_18
-- name    : ROGCones.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:46.451482+00:00
-- url     : https://prove2.me/theorems/16227053-bc51-4763-83f3-aca3a12249a6
-- title:
--   Lemma 18 — for $n \ge 4$, if (i) fails some $\alpha_1M_1+\alpha_2M_2$ has rank $\ge 3$
-- statement:
--   Let $n \ge 4$, $M_1, M_2 \in \mathbb S^n$, $\mathcal M = \{M_1, M_2\}$, and suppose Assumption 1 holds. If condition (i) does not hold, then there exist $(\alpha_1, \alpha_2)$ with
--   $$
--   \operatorname{rank}(\alpha_1 M_1 + \alpha_2 M_2) \ge 3 .
--   $$
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: 𝓜 = {M₁, M₂} ⊆ 𝕊ⁿ → two symmetric matrices M₁, M₂ and the set {M₁, M₂}, M₁ = M₂ allowed; reason: the printed set {M₁, M₂} does not require M₁ ≠ M₂; same instances
--   - encoding: Assumption 1: span(⋃_{M∈𝓜} range(M)) = ℝⁿ → Assumption1 {M₁, M₂}, i.e. Submodule.span ℝ (⋃ M ∈ 𝓜, Set.range M.mulVec) = ⊤; reason: range(M) is the column space; same instances
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Lemma 18, p.19

import Mathlib
import Definitions.Def_ROGCones_CondI
import Definitions.Def_ROGCones_Assumption1

namespace ROGCones

/-- **Lemma 18 — for `n ≥ 4`, if (i) fails some combination of `M₁, M₂` has rank at least 3.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Lemma 18, p.19: "Let 𝓜 = {M₁, M₂}. Suppose
Assumption 1 holds and n ≥ 4. If condition (i) in Theorem 4 does not hold, then there exists
(α₁, α₂) such that rank(α₁M₁ + α₂M₂) ≥ 3."

**Formalization Note.** `M₁, M₂` symmetric; `(α₁, α₂)` is unrestricted, as printed (it is
necessarily nonzero). -/
theorem lemma_18 {n : ℕ} (hn : 4 ≤ n) (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ) (hM₁ : M₁.IsSymm)
    (hM₂ : M₂.IsSymm) (hA : Assumption1 {M₁, M₂}) (hI : ¬ CondI M₁ M₂) :
    ∃ α₁ α₂ : ℝ, 3 ≤ (α₁ • M₁ + α₂ • M₂).rank := by sorry

end ROGCones
