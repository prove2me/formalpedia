-- Prove2me | Theorems.Thm_ROGCones_lemma_3
-- name    : ROGCones.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:49.363978+00:00
-- url     : https://prove2.me/theorems/3c10d357-e1b7-4022-9ed0-e8110ebf8ac4
-- title:
--   Lemma 3 — $\mathcal S(\mathcal M)$ is ROG iff all its faces are iff all slices $\mathcal S(\mathcal M)\cap\mathcal T(\mathcal M')$ are
-- statement:
--   Let $\mathcal M \subseteq \mathbb S^n$ be any set. The following are equivalent:
--
--   1. $\mathcal S(\mathcal M)$ is ROG.
--   2. Every face of $\mathcal S(\mathcal M)$ is ROG.
--   3. $\mathcal S(\mathcal M) \cap \mathcal T(\mathcal M')$ is ROG for every $\mathcal M' \subseteq \mathcal M$.
--
--   So the ROG property passes to faces and to the sets obtained by turning some of the inequalities into equalities.
--
--   **Formalization Note** A face of $\mathcal S(\mathcal M)$ is a convex subset $F$ that is extreme in Mathlib's sense (`IsExtreme ℝ (SCone 𝓜) F`); the empty face is included and is trivially ROG. The equivalence is a `List.TFAE`.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: 𝓜 ⊆ 𝕊ⁿ → a Set of matrices with ∀ M ∈ 𝓜, M.IsSymm; reason: same instances
--   - encoding: face of 𝒮(𝓜) → a convex F with IsExtreme ℝ (SCone 𝓜) F (empty face allowed); reason: the standard notion of face of a convex set; the empty face is ROG, so including it changes nothing
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Lemma 3, p.7

import Mathlib
import Definitions.Def_ROGCones_SCone
import Definitions.Def_ROGCones_TCone
import Definitions.Def_ROGCones_IsROG

namespace ROGCones

/-- **Lemma 3 — ROG of `𝒮(𝓜)`, of all its faces, and of all its slices `𝒮(𝓜) ∩ 𝒯(𝓜')` are
equivalent.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Lemma 3, p.7: "For any set 𝓜 ⊆ Sⁿ, the
following are equivalent: 1. 𝒮(𝓜) is ROG. 2. Every face of 𝒮(𝓜) is ROG. 3. 𝒮(𝓜) ∩ 𝒯(𝓜′) is
ROG for every 𝓜′ ⊆ 𝓜."

**Formalization Note.** `𝓜 ⊆ Sⁿ` is `∀ M ∈ 𝓜, M.IsSymm`. A face of `𝒮(𝓜)` is a convex set `F`
with `IsExtreme ℝ (SCone 𝓜) F` (Mathlib: `F ⊆ 𝒮(𝓜)` and any open segment of `𝒮(𝓜)` meeting `F`
has both endpoints in `F`); the empty face is allowed and is ROG. The three statements are a
`List.TFAE`. -/
theorem lemma_3 {n : ℕ} (𝓜 : Set (Matrix (Fin n) (Fin n) ℝ)) (h𝓜 : ∀ M ∈ 𝓜, M.IsSymm) :
    List.TFAE
      [IsROG (SCone 𝓜),
        ∀ F : Set (Matrix (Fin n) (Fin n) ℝ), Convex ℝ F → IsExtreme ℝ (SCone 𝓜) F → IsROG F,
        ∀ 𝓜' ⊆ 𝓜, IsROG (SCone 𝓜 ∩ TCone 𝓜')] := by sorry

end ROGCones
