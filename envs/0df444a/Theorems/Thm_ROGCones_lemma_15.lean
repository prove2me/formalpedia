-- Prove2me | Theorems.Thm_ROGCones_lemma_15
-- name    : ROGCones.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:01.033326+00:00
-- url     : https://prove2.me/theorems/7dc6c7af-8ff6-4cc8-a9d0-eff8d07b22e9
-- title:
--   Lemma 15 — restricting $\mathcal M$ to its joint range preserves ROG of $\mathcal T$ and conditions (i), (ii)
-- statement:
--   Let $\mathcal M \subseteq \mathbb S^n$ and let $W = \operatorname{span}\bigl(\bigcup_{M\in\mathcal M}\operatorname{range}(M)\bigr)$, of dimension $k$. Let $U$ be an $n\times k$ matrix whose columns form a basis of $W$, and for $M \in \mathcal M$ let $\overline M = U^\top M U \in \mathbb S^k$ be the restriction of $M$ to $W$; put $\overline{\mathcal M} = \{\overline M : M \in \mathcal M\}$. Then:
--
--   1. $\mathcal T(\mathcal M)$ is ROG if and only if $\mathcal T(\overline{\mathcal M})$ is ROG;
--   2. if $\mathcal M = \{M_1, M_2\}$, then condition (i) holds for $(M_1, M_2)$ iff it holds for $(\overline M_1, \overline M_2)$, and condition (ii) holds for $(M_1, M_2)$ iff it holds for $(\overline M_1, \overline M_2)$.
--
--   This lets the proof of Theorem 4 assume that the ranges of $M_1, M_2$ span $\mathbb R^n$ (Assumption 1).
--
--   **Formalization Note** The paper identifies $W$ with $\mathbb R^{\dim W}$ and uses the inclusion map; here $U$ is any injective linear map $\mathbb R^k \to \mathbb R^n$ with image $W$, which includes the orthonormal choice.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: 𝓜 ⊆ 𝕊ⁿ → a Set of matrices with ∀ M ∈ 𝓜, M.IsSymm; reason: same instances
--   - generalization: M_W := UᵀMU with U : W → ℝⁿ the inclusion (W identified with ℝ^{dim W}) → M̄ := UᵀMU for any n × k matrix U with injective mulVec and span of its range = W; reason: an orthonormal basis matrix of W is the paper's inclusion map, so the source's statement is the special case
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Lemma 15, p.16

import Mathlib
import Definitions.Def_ROGCones_TCone
import Definitions.Def_ROGCones_IsROG
import Definitions.Def_ROGCones_CondI
import Definitions.Def_ROGCones_CondII
import Definitions.Def_ROGCones_JointRange

namespace ROGCones

/-- **Lemma 15 — restricting to the joint range preserves ROG of `𝒯` and conditions (i), (ii).**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Lemma 15, p.16: "Let W := span(⋃_{M∈𝓜}
range(M)). For M ∈ 𝓜, let M̄ = M_W denote the restriction of M to W. Let 𝓜̄ = {M̄ : M ∈ 𝓜}.
Then, 𝒯(𝓜) is ROG if and only 𝒯(𝓜̄) is ROG. Furthermore, if 𝓜 = {M₁, M₂} and 𝓜̄ = {M̄₁, M̄₂},
then each of conditions (i) and (ii) in Theorem 4 hold for 𝓜 if and only if they hold for 𝓜̄."

**Formalization Note.** The paper identifies `W` with `ℝ^{dim W}` and sets `M_W := UᵀMU` with
`U : W → ℝⁿ` the inclusion (§1.4, p.5). Here `U` is any `n × k` real matrix whose map
`ℝᵏ → ℝⁿ` is injective with range `W` (a basis matrix of `W`, so `k = dim W`), and
`M̄ = UᵀMU : Matrix (Fin k) (Fin k) ℝ`. Choosing `U` with orthonormal columns gives the paper's
identification; any other basis is allowed. `𝓜 ⊆ Sⁿ` is `∀ M ∈ 𝓜, M.IsSymm`. -/
theorem lemma_15 {n k : ℕ} (𝓜 : Set (Matrix (Fin n) (Fin n) ℝ)) (h𝓜 : ∀ M ∈ 𝓜, M.IsSymm)
    (U : Matrix (Fin n) (Fin k) ℝ) (hU_inj : Function.Injective U.mulVec)
    (hU_range : Submodule.span ℝ (Set.range U.mulVec) = JointRange 𝓜) :
    (IsROG (TCone 𝓜) ↔ IsROG (TCone ((fun M => U.transpose * M * U) '' 𝓜))) ∧
      ∀ M₁ M₂ : Matrix (Fin n) (Fin n) ℝ, 𝓜 = {M₁, M₂} →
        (CondI M₁ M₂ ↔ CondI (U.transpose * M₁ * U) (U.transpose * M₂ * U)) ∧
          (CondII M₁ M₂ ↔ CondII (U.transpose * M₁ * U) (U.transpose * M₂ * U)) := by sorry

end ROGCones
