-- Prove2me | Theorems.Thm_ROGCones_lemma_12
-- name    : ROGCones.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:35.36558+00:00
-- url     : https://prove2.me/theorems/f141d985-4e26-4cb5-9fd1-ed447a3ebb3f
-- title:
--   Lemma 12 (Sturm–Zhang) — the PSD cone cut by a single LMI is ROG
-- statement:
--   For every $n$ and every symmetric matrix $M \in \mathbb S^n$, the cone
--   $$
--   \mathcal S(\{M\}) = \{X \in \mathbb S^n_+ : \langle M, X\rangle \ge 0\}
--   $$
--   is rank-one generated. This is the conic form of the S-lemma, due to Sturm and Zhang.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Lemma 12, p.11

import Mathlib
import Definitions.Def_ROGCones_SCone
import Definitions.Def_ROGCones_IsROG

namespace ROGCones

/-- **Lemma 12 (Sturm and Zhang [28]) — the PSD cone cut by one LMI is ROG.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Lemma 12, p.11: "Consider any M ∈ Sⁿ, and let
𝓜 = {M}. Then 𝒮(𝓜) is ROG."

**Formalization Note.** `M ∈ Sⁿ` is `M.IsSymm`; `n` is arbitrary (including `0`). -/
theorem lemma_12 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    IsROG (SCone {M}) := by sorry

end ROGCones
