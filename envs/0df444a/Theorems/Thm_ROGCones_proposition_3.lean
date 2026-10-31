-- Prove2me | Theorems.Thm_ROGCones_proposition_3
-- name    : ROGCones.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:54.264093+00:00
-- url     : https://prove2.me/theorems/d021ce7c-6491-43ba-bafe-0851931516a3
-- title:
--   Proposition 3 — Theorem 4 for $n = 3$
-- statement:
--   Let $M_1, M_2 \in \mathbb S^3$, $\mathcal M = \{M_1, M_2\}$, and suppose Assumption 1 holds. If $\mathcal T(\mathcal M)$ is ROG, then condition (i) or condition (ii) holds:
--
--   1. there is $(\alpha_1,\alpha_2)\neq(0,0)$ with $\alpha_1M_1+\alpha_2M_2 \in \mathbb S^3_+$, or
--   2. there are $a, b, c \in \mathbb R^3$ with $M_1 = \mathrm{Sym}(ac^\top)$ and $M_2 = \mathrm{Sym}(bc^\top)$.
--
--   **Formalization Note** $n = 3$ is encoded by the type `Matrix (Fin 3) (Fin 3) ℝ`.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: 𝓜 = {M₁, M₂} ⊆ 𝕊ⁿ → two symmetric matrices M₁, M₂ and the set {M₁, M₂}, M₁ = M₂ allowed; reason: the printed set {M₁, M₂} does not require M₁ ≠ M₂; same instances
--   - encoding: Assumption 1: span(⋃_{M∈𝓜} range(M)) = ℝⁿ → Assumption1 {M₁, M₂}, i.e. Submodule.span ℝ (⋃ M ∈ 𝓜, Set.range M.mulVec) = ⊤; reason: range(M) is the column space; same instances
--   - encoding: n = 3 → Matrix (Fin 3) (Fin 3) ℝ; reason: same instances
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Proposition 3, p.18

import Mathlib
import Definitions.Def_ROGCones_TCone
import Definitions.Def_ROGCones_IsROG
import Definitions.Def_ROGCones_CondI
import Definitions.Def_ROGCones_CondII
import Definitions.Def_ROGCones_Assumption1

namespace ROGCones

/-- **Proposition 3 — Theorem 4 in dimension `n = 3`.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Proposition 3, p.18: "Let 𝓜 = {M₁, M₂}. Suppose
Assumption 1 holds and n = 3. If 𝒯(𝓜) is ROG, then one of conditions (i) or (ii) of Theorem 4
must hold."

**Formalization Note.** `n = 3` is the matrix type `Matrix (Fin 3) (Fin 3) ℝ`; `M₁, M₂`
symmetric; conditions (i), (ii) are `CondI`, `CondII`. -/
theorem proposition_3 (M₁ M₂ : Matrix (Fin 3) (Fin 3) ℝ) (hM₁ : M₁.IsSymm) (hM₂ : M₂.IsSymm)
    (hA : Assumption1 {M₁, M₂}) (hT : IsROG (TCone {M₁, M₂})) :
    CondI M₁ M₂ ∨ CondII M₁ M₂ := by sorry

end ROGCones
