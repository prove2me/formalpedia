-- Prove2me | Theorems.Thm_ROGCones_lemma_13
-- name    : ROGCones.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:52.397858+00:00
-- url     : https://prove2.me/theorems/4e1f6680-c9c0-409b-9f7c-1b3cdec3540c
-- title:
--   Lemma 13 — a nontrivial PSD combination of $M_1, M_2$ makes $\mathcal S(\{M_1,M_2\})$ ROG
-- statement:
--   Let $M_1, M_2 \in \mathbb S^n$ and $\mathcal M = \{M_1, M_2\}$. If there is $(\alpha_1, \alpha_2) \neq (0,0)$ with
--   $$
--   \alpha_1 M_1 + \alpha_2 M_2 \in \mathbb S^n_+ ,
--   $$
--   then $\mathcal S(\mathcal M)$ is ROG. This is the "if" direction of the main theorem under condition (i).
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: 𝓜 = {M₁, M₂} ⊆ 𝕊ⁿ → two symmetric matrices M₁, M₂ and the set {M₁, M₂}, M₁ = M₂ allowed; reason: the printed set {M₁, M₂} does not require M₁ ≠ M₂; same instances
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Lemma 13, p.12

import Mathlib
import Definitions.Def_ROGCones_SCone
import Definitions.Def_ROGCones_IsROG

namespace ROGCones

/-- **Lemma 13 — a nontrivial PSD combination makes `𝒮({M₁, M₂})` ROG.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Lemma 13, p.12: "Let 𝓜 = {M₁, M₂} and suppose
there exists (α₁, α₂) ≠ (0, 0) such that α₁M₁ + α₂M₂ ∈ Sⁿ₊. Then, 𝒮(𝓜) is ROG."

**Formalization Note.** `M₁, M₂` symmetric (𝓜 ⊆ Sⁿ); `M₁ = M₂` is allowed. Sⁿ₊ membership is
`Matrix.PosSemidef`. -/
theorem lemma_13 {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ) (hM₁ : M₁.IsSymm) (hM₂ : M₂.IsSymm)
    (h : ∃ α₁ α₂ : ℝ, (α₁, α₂) ≠ (0, 0) ∧ (α₁ • M₁ + α₂ • M₂).PosSemidef) :
    IsROG (SCone {M₁, M₂}) := by sorry

end ROGCones
