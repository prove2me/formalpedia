-- Prove2me | Theorems.Thm_ROGCones_lemma_17
-- name    : ROGCones.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:36.860996+00:00
-- url     : https://prove2.me/theorems/da5315b5-ffa8-4789-9b2e-1ec671b83a37
-- title:
--   Lemma 17 — for $n = 3$, if (i) and (ii) fail, $\mathcal N(\mathcal M)$ is a union of at most four lines
-- statement:
--   Let $M_1, M_2 \in \mathbb S^3$, $\mathcal M = \{M_1, M_2\}$, and suppose Assumption 1 holds. If neither condition (i) nor condition (ii) holds for $(M_1, M_2)$, then
--   $$
--   \mathcal N(\mathcal M) = \ell_1 \cup \dots \cup \ell_m, \qquad m \le 4,
--   $$
--   where each $\ell_j$ is a one-dimensional subspace of $\mathbb R^3$. The proof in the paper (Appendix A) is elementary linear algebra; it is also a consequence of Bézout's theorem.
--
--   **Formalization Note** The lines form a `Finset` of submodules of `Fin 3 → ℝ` with at most four elements, each of `finrank` one, and the conclusion is a set equality.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: 𝓜 = {M₁, M₂} ⊆ 𝕊ⁿ → two symmetric matrices M₁, M₂ and the set {M₁, M₂}, M₁ = M₂ allowed; reason: the printed set {M₁, M₂} does not require M₁ ≠ M₂; same instances
--   - encoding: Assumption 1: span(⋃_{M∈𝓜} range(M)) = ℝⁿ → Assumption1 {M₁, M₂}, i.e. Submodule.span ℝ (⋃ M ∈ 𝓜, Set.range M.mulVec) = ⊤; reason: range(M) is the column space; same instances
--   - encoding: n = 3 → Matrix (Fin 3) (Fin 3) ℝ; reason: same instances
--   - encoding: the union of at most four one-dimensional subspaces of ℝ³ → ∃ L : Finset (Submodule ℝ (Fin 3 → ℝ)), L.card ≤ 4, each finrank 1, NSet {M₁, M₂} = ⋃ l ∈ L, l; reason: same statement
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Lemma 17, p.18 (proof in Appendix A, pp.30–31)

import Mathlib
import Definitions.Def_ROGCones_NSet
import Definitions.Def_ROGCones_CondI
import Definitions.Def_ROGCones_CondII
import Definitions.Def_ROGCones_Assumption1

namespace ROGCones

/-- **Lemma 17 — for `n = 3`, if (i) and (ii) fail, `𝒩(𝓜)` is a union of at most four lines.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Lemma 17, p.18 (proof in Appendix A,
pp.30–31): "Let 𝓜 = {M₁, M₂}. Suppose Assumption 1 holds and n = 3. If neither conditions (i)
nor (ii) of Theorem 4 hold, then 𝒩(𝓜) is the union of at most four one-dimensional subspaces of
ℝ³."

**Formalization Note.** `n = 3` is the matrix type `Matrix (Fin 3) (Fin 3) ℝ`, ℝ³ is
`Fin 3 → ℝ`; `M₁, M₂` symmetric. "The union of at most four one-dimensional subspaces" is a
`Finset` `L` of submodules with `L.card ≤ 4`, each of `finrank` 1, and the set equality
`𝒩(𝓜) = ⋃_{ℓ ∈ L} ℓ`. -/
theorem lemma_17 (M₁ M₂ : Matrix (Fin 3) (Fin 3) ℝ) (hM₁ : M₁.IsSymm) (hM₂ : M₂.IsSymm)
    (hA : Assumption1 {M₁, M₂}) (hI : ¬ CondI M₁ M₂) (hII : ¬ CondII M₁ M₂) :
    ∃ L : Finset (Submodule ℝ (Fin 3 → ℝ)), L.card ≤ 4 ∧
      (∀ l ∈ L, Module.finrank ℝ l = 1) ∧
      NSet {M₁, M₂} = ⋃ l ∈ L, (l : Set (Fin 3 → ℝ)) := by sorry

end ROGCones
