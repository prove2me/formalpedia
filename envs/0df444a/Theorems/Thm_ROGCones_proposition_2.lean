-- Prove2me | Theorems.Thm_ROGCones_proposition_2
-- name    : ROGCones.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:23.536606+00:00
-- url     : https://prove2.me/theorems/6419acbf-4f16-4bdc-a2b1-ab5f1f6d080d
-- title:
--   Proposition 2 — Theorem 4 for $n = 2$
-- statement:
--   Let $M_1, M_2 \in \mathbb S^2$, $\mathcal M = \{M_1, M_2\}$, and suppose Assumption 1 holds, i.e. $\operatorname{range}(M_1) + \operatorname{range}(M_2) = \mathbb R^2$. If $\mathcal T(\mathcal M)$ is ROG, then there is $(\alpha_1, \alpha_2) \neq (0,0)$ with
--   $$
--   \alpha_1 M_1 + \alpha_2 M_2 \in \mathbb S^2_+ .
--   $$
--
--   **Formalization Note** $n = 2$ is encoded by the type of $2\times 2$ matrices `Matrix (Fin 2) (Fin 2) ℝ`.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: 𝓜 = {M₁, M₂} ⊆ 𝕊ⁿ → two symmetric matrices M₁, M₂ and the set {M₁, M₂}, M₁ = M₂ allowed; reason: the printed set {M₁, M₂} does not require M₁ ≠ M₂; same instances
--   - encoding: Assumption 1: span(⋃_{M∈𝓜} range(M)) = ℝⁿ → Assumption1 {M₁, M₂}, i.e. Submodule.span ℝ (⋃ M ∈ 𝓜, Set.range M.mulVec) = ⊤; reason: range(M) is the column space; same instances
--   - encoding: n = 2 → Matrix (Fin 2) (Fin 2) ℝ; reason: same instances
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Proposition 2, p.17

import Mathlib
import Definitions.Def_ROGCones_TCone
import Definitions.Def_ROGCones_IsROG
import Definitions.Def_ROGCones_Assumption1

namespace ROGCones

/-- **Proposition 2 — Theorem 4 in dimension `n = 2`.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Proposition 2, p.17: "Let 𝓜 = {M₁, M₂}. Suppose
Assumption 1 holds and n = 2. If 𝒯(𝓜) is ROG then there exists (α₁, α₂) ≠ (0, 0) such that
α₁M₁ + α₂M₂ ∈ Sⁿ₊."

**Formalization Note.** `n = 2` is encoded by the matrix type `Matrix (Fin 2) (Fin 2) ℝ`;
`M₁, M₂` symmetric; Assumption 1 is `Assumption1 {M₁, M₂}` (the ranges of `M₁, M₂` span ℝ²). -/
theorem proposition_2 (M₁ M₂ : Matrix (Fin 2) (Fin 2) ℝ) (hM₁ : M₁.IsSymm) (hM₂ : M₂.IsSymm)
    (hA : Assumption1 {M₁, M₂}) (hT : IsROG (TCone {M₁, M₂})) :
    ∃ α₁ α₂ : ℝ, (α₁, α₂) ≠ (0, 0) ∧ (α₁ • M₁ + α₂ • M₂).PosSemidef := by sorry

end ROGCones
