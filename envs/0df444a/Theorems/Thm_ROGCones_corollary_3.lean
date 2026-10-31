-- Prove2me | Theorems.Thm_ROGCones_corollary_3
-- name    : ROGCones.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:45.909738+00:00
-- url     : https://prove2.me/theorems/9b8851a3-70eb-479a-ac80-2b10deadc3e6
-- title:
--   Corollary 3 — for two LMIs, $\mathcal S(\mathcal M)$ is ROG iff $\mathcal T(\mathcal M)$ is ROG
-- statement:
--   Let $M_1, M_2 \in \mathbb S^n$ and $\mathcal M = \{M_1, M_2\}$. Then
--   $$
--   \mathcal S(\mathcal M) \text{ is ROG} \iff \mathcal T(\mathcal M) \text{ is ROG}.
--   $$
--   This reduces the main theorem to the equality-constrained cone $\mathcal T(\mathcal M)$.
--
--   **Formalization Note** The paper assumes $|\mathcal M| = 2$; the Lean statement allows $M_1 = M_2$ as well.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - generalization: |𝓜| = 2 → any two symmetric M₁, M₂, M₁ = M₂ allowed; reason: for M₁ ≠ M₂ it is the source's statement; for M₁ = M₂ both sides hold (Lemma 12 and Corollary 1)
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Corollary 3, p.12

import Mathlib
import Definitions.Def_ROGCones_SCone
import Definitions.Def_ROGCones_TCone
import Definitions.Def_ROGCones_IsROG

namespace ROGCones

/-- **Corollary 3 — for two LMIs, `𝒮(𝓜)` is ROG iff `𝒯(𝓜)` is ROG.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Corollary 3, p.12: "Suppose |𝓜| = 2, then
𝒮(𝓜) is ROG if and only if 𝒯(𝓜) is ROG."

**Formalization Note.** `𝓜 = {M₁, M₂}` with `M₁, M₂` symmetric. `M₁ = M₂` is not excluded, so
the statement also covers `|𝓜| = 1` (where both sides hold by Lemma 12 and Corollary 1). -/
theorem corollary_3 {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ) (hM₁ : M₁.IsSymm)
    (hM₂ : M₂.IsSymm) :
    IsROG (SCone {M₁, M₂}) ↔ IsROG (TCone {M₁, M₂}) := by sorry

end ROGCones
