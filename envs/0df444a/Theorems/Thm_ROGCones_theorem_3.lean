-- Prove2me | Theorems.Thm_ROGCones_theorem_3
-- name    : ROGCones.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:04.031991+00:00
-- url     : https://prove2.me/theorems/de519631-2760-4fe4-8f14-14ea8116c31c
-- title:
--   Theorem 3 — $\mathcal S(\{M_1,M_2\})$ is ROG iff (i) a nontrivial combination is PSD or (ii) $M_1=\mathrm{Sym}(ac^\top)$, $M_2=\mathrm{Sym}(bc^\top)$
-- statement:
--   Let $M_1, M_2 \in \mathbb S^n$ and $\mathcal M = \{M_1, M_2\}$. Then the cone
--   $$
--   \mathcal S(\mathcal M) = \{X \in \mathbb S^n_+ : \langle M_1, X\rangle \ge 0,\ \langle M_2, X\rangle \ge 0\}
--   $$
--   is rank-one generated, i.e. $\mathcal S(\mathcal M) = \operatorname{conv}\bigl(\mathcal S(\mathcal M) \cap \{xx^\top : x\in\mathbb R^n\}\bigr)$, if and only if one of the following holds:
--
--   1. there exists $(\alpha_1, \alpha_2) \neq (0,0)$ such that $\alpha_1 M_1 + \alpha_2 M_2 \in \mathbb S^n_+$, or
--   2. there exist $a, b, c \in \mathbb R^n$ such that $M_1 = \mathrm{Sym}(ac^\top)$ and $M_2 = \mathrm{Sym}(bc^\top)$.
--
--   This is the paper's complete characterization of rank-one generated cones defined by two linear matrix inequalities: the property is certified either by a PSD aggregation of the constraints or by a common rank-two structure.
--
--   **Formalization Note** The statement holds for every $n$ (including $n = 0$) and every pair of symmetric matrices, with no Assumption 1; $\langle M, X\rangle$ is `(M * X).trace`.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: 𝓜 = {M₁, M₂} ⊆ 𝕊ⁿ → two symmetric matrices M₁, M₂ and the set {M₁, M₂}, M₁ = M₂ allowed; reason: the printed set {M₁, M₂} does not require M₁ ≠ M₂; same instances
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Theorem 3, p.15

import Mathlib
import Definitions.Def_ROGCones_SCone
import Definitions.Def_ROGCones_IsROG
import Definitions.Def_ROGCones_CondI
import Definitions.Def_ROGCones_CondII

namespace ROGCones

/-- **Theorem 3 — the PSD cone cut by two LMIs is ROG iff (i) or (ii) holds.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Theorem 3, p.15: "Let 𝓜 = {M₁, M₂}. Then,
𝒮(𝓜) is ROG if and only if one of the following holds: (i) there exists (α₁, α₂) ≠ (0, 0) such
that α₁M₁ + α₂M₂ ∈ Sⁿ₊, or (ii) there exists a, b, c ∈ ℝⁿ such that M₁ = Sym(ac⊤) and
M₂ = Sym(bc⊤)."

**Formalization Note.** Every `n` (including `0`) and every pair of symmetric matrices
(`𝓜 ⊆ Sⁿ`; `M₁ = M₂` is allowed). `𝒮(𝓜)` is `SCone {M₁, M₂}` with `⟨M, X⟩ = tr(MX)`; ROG is
`IsROG`; conditions (i), (ii) are `CondI` (with `(α₁, α₂) ≠ (0, 0)`) and `CondII` (a common
`c`). -/
theorem theorem_3 {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ) (hM₁ : M₁.IsSymm)
    (hM₂ : M₂.IsSymm) :
    IsROG (SCone {M₁, M₂}) ↔ CondI M₁ M₂ ∨ CondII M₁ M₂ := by sorry

end ROGCones
