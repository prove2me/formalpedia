-- Prove2me | Theorems.Thm_ROGCones_theorem_4
-- name    : ROGCones.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:49.383537+00:00
-- url     : https://prove2.me/theorems/57ca9697-d426-4a94-95a1-f9c6ad25eabb
-- title:
--   Theorem 4 — if $\mathcal T(\{M_1,M_2\})$ is ROG then condition (i) or (ii) holds
-- statement:
--   Let $M_1, M_2 \in \mathbb S^n$ and $\mathcal M = \{M_1, M_2\}$. If $\mathcal T(\mathcal M)$ is ROG, then one of the following holds:
--
--   1. there exists $(\alpha_1, \alpha_2) \neq (0,0)$ such that $\alpha_1 M_1 + \alpha_2 M_2 \in \mathbb S^n_+$, or
--   2. there exist $a, b, c \in \mathbb R^n$ such that $M_1 = \mathrm{Sym}(ac^\top)$ and $M_2 = \mathrm{Sym}(bc^\top)$.
--
--   Together with Corollary 3 this is the "only if" direction of the main theorem. There is no dimension restriction and no Assumption 1.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: 𝓜 = {M₁, M₂} ⊆ 𝕊ⁿ → two symmetric matrices M₁, M₂ and the set {M₁, M₂}, M₁ = M₂ allowed; reason: the printed set {M₁, M₂} does not require M₁ ≠ M₂; same instances
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Theorem 4, p.15

import Mathlib
import Definitions.Def_ROGCones_TCone
import Definitions.Def_ROGCones_IsROG
import Definitions.Def_ROGCones_CondI
import Definitions.Def_ROGCones_CondII

namespace ROGCones

/-- **Theorem 4 — if `𝒯({M₁, M₂})` is ROG, then condition (i) or (ii) holds.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Theorem 4, p.15: "Let 𝓜 = {M₁, M₂}. If 𝒯(𝓜)
is ROG, then one of the following holds: (i) there exists (α₁, α₂) ≠ (0, 0) such that
α₁M₁ + α₂M₂ ∈ Sⁿ₊, or (ii) there exists a, b, c ∈ ℝⁿ such that M₁ = Sym(ac⊤) and M₂ = Sym(bc⊤)."

**Formalization Note.** Every `n`, every symmetric pair (`M₁ = M₂` allowed), no Assumption 1.
Conditions (i), (ii) are `CondI`, `CondII`. -/
theorem theorem_4 {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ) (hM₁ : M₁.IsSymm)
    (hM₂ : M₂.IsSymm) (hT : IsROG (TCone {M₁, M₂})) :
    CondI M₁ M₂ ∨ CondII M₁ M₂ := by sorry

end ROGCones
