-- Prove2me | Theorems.Thm_ROGCones_lemma_16
-- name    : ROGCones.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:50.064788+00:00
-- url     : https://prove2.me/theorems/e42b3e2b-68fb-487f-98e0-364cdcdd6db7
-- title:
--   Lemma 16 (Hildebrand) — in a ROG cone $\mathcal T(\mathcal M)$, $X$ is a sum of $\mathrm{rank}(X)$ terms $x_ix_i^\top$, $x_i \in \mathcal N(\mathcal M)$
-- statement:
--   Let $\mathcal M \subseteq \mathbb S^n$ and suppose $\mathcal T(\mathcal M)$ is ROG. Then every $X \in \mathcal T(\mathcal M)$ can be written as
--   $$
--   X = \sum_{i=1}^{r} x_i x_i^\top, \qquad x_i \in \mathcal N(\mathcal M) \text{ for all } i \in [r], \qquad r = \operatorname{rank}(X).
--   $$
--   So the Carathéodory number of $X$ in a ROG cone $\mathcal T(\mathcal M)$ equals its rank. The paper cites this from Hildebrand [18, Lemma 3.13].
--
--   **Formalization Note** The terms are indexed by `Fin X.rank`, so the number of terms is exactly $\operatorname{rank}(X)$; for $X = 0$ the sum is empty.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: 𝓜 ⊆ 𝕊ⁿ → a Set of matrices with ∀ M ∈ 𝓜, M.IsSymm; reason: same instances
--   - encoding: r = rank(X) terms → x : Fin X.rank → (Fin n → ℝ); reason: same instances
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Lemma 16 ([18, Lemma 3.13]), p.18

import Mathlib
import Definitions.Def_ROGCones_TCone
import Definitions.Def_ROGCones_NSet
import Definitions.Def_ROGCones_IsROG

namespace ROGCones

/-- **Lemma 16 ([18, Lemma 3.13]) — in a ROG cone `𝒯(𝓜)`, every `X` is a sum of `rank(X)` rank-one
terms `xᵢxᵢᵀ` with `xᵢ ∈ 𝒩(𝓜)`.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Lemma 16 ([18, Lemma 3.13]), p.18: "Suppose
𝒯(𝓜) is ROG. For every X ∈ 𝒯(𝓜), we can write X = ∑_{i=1}^r xᵢxᵢ⊤ where xᵢ ∈ 𝒩(𝓜) for all
i ∈ [r] and r = rank(X)."

**Formalization Note.** `𝓜 ⊆ Sⁿ` is `∀ M ∈ 𝓜, M.IsSymm`; the number of terms is exactly
`X.rank` (indices `Fin X.rank`), which is the content of the lemma; `xxᵀ` is
`Matrix.vecMulVec x x`. For `X = 0` the sum is empty. -/
theorem lemma_16 {n : ℕ} (𝓜 : Set (Matrix (Fin n) (Fin n) ℝ)) (h𝓜 : ∀ M ∈ 𝓜, M.IsSymm)
    (hT : IsROG (TCone 𝓜)) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X ∈ TCone 𝓜) :
    ∃ x : Fin X.rank → (Fin n → ℝ), (∀ i, x i ∈ NSet 𝓜) ∧
      X = ∑ i, Matrix.vecMulVec (x i) (x i) := by sorry

end ROGCones
