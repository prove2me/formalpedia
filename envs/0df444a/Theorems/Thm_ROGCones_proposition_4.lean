-- Prove2me | Theorems.Thm_ROGCones_proposition_4
-- name    : ROGCones.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:31.602118+00:00
-- url     : https://prove2.me/theorems/84713e7b-e829-4ff1-82ad-f6d8dd0d5762
-- title:
--   Proposition 4 — Theorem 4 for $n \ge 4$
-- statement:
--   Let $n \ge 4$, $M_1, M_2 \in \mathbb S^n$, $\mathcal M = \{M_1, M_2\}$, and suppose Assumption 1 holds. If $\mathcal T(\mathcal M)$ is ROG, then there is $(\alpha_1, \alpha_2) \neq (0,0)$ with
--   $$
--   \alpha_1 M_1 + \alpha_2 M_2 \in \mathbb S^n_+ .
--   $$
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: 𝓜 = {M₁, M₂} ⊆ 𝕊ⁿ → two symmetric matrices M₁, M₂ and the set {M₁, M₂}, M₁ = M₂ allowed; reason: the printed set {M₁, M₂} does not require M₁ ≠ M₂; same instances
--   - encoding: Assumption 1: span(⋃_{M∈𝓜} range(M)) = ℝⁿ → Assumption1 {M₁, M₂}, i.e. Submodule.span ℝ (⋃ M ∈ 𝓜, Set.range M.mulVec) = ⊤; reason: range(M) is the column space; same instances
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Proposition 4, p.19

import Mathlib
import Definitions.Def_ROGCones_TCone
import Definitions.Def_ROGCones_IsROG
import Definitions.Def_ROGCones_Assumption1

namespace ROGCones

/-- **Proposition 4 — Theorem 4 in dimensions `n ≥ 4`.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Proposition 4, p.19: "Let 𝓜 = {M₁, M₂}. Suppose
Assumption 1 holds and n ≥ 4. If 𝒯(𝓜) is ROG, then there exists (α₁, α₂) ≠ (0, 0) such that
α₁M₁ + α₂M₂ ∈ Sⁿ₊."

**Formalization Note.** `M₁, M₂` symmetric; Sⁿ₊ is `Matrix.PosSemidef`. -/
theorem proposition_4 {n : ℕ} (hn : 4 ≤ n) (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ)
    (hM₁ : M₁.IsSymm) (hM₂ : M₂.IsSymm) (hA : Assumption1 {M₁, M₂})
    (hT : IsROG (TCone {M₁, M₂})) :
    ∃ α₁ α₂ : ℝ, (α₁, α₂) ≠ (0, 0) ∧ (α₁ • M₁ + α₂ • M₂).PosSemidef := by sorry

end ROGCones
