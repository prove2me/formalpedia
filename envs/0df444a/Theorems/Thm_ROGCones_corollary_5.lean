-- Prove2me | Theorems.Thm_ROGCones_corollary_5
-- name    : ROGCones.corollary_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:37.640691+00:00
-- url     : https://prove2.me/theorems/7af32527-d119-4e09-9392-1873ae9d5254
-- title:
--   Corollary 5 — $\{X \succeq 0 : a^\top Xc \ge 0,\ b^\top Xc \ge 0\}$ is ROG
-- statement:
--   Let $a, b, c \in \mathbb R^n$. Then the set
--   $$
--   \{X \in \mathbb S^n_+ : a^\top X c \ge 0,\ b^\top X c \ge 0\}
--   $$
--   is rank-one generated. Since $a^\top X c = \langle \mathrm{Sym}(ac^\top), X\rangle$ for symmetric $X$, this is the "if" direction of the main theorem under condition (ii).
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Corollary 5, p.13

import Mathlib
import Definitions.Def_ROGCones_IsROG

open Matrix

namespace ROGCones

/-- **Corollary 5 — `{X ⪰ 0 : aᵀXc ≥ 0, bᵀXc ≥ 0}` is ROG.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Corollary 5, p.13: "Let a, b, c ∈ ℝⁿ. Then the
set {X ∈ Sⁿ₊ : a⊤Xc ≥ 0, b⊤Xc ≥ 0} is ROG."

**Formalization Note.** ℝⁿ is `Fin n → ℝ`; `aᵀXc` is `a ⬝ᵥ (X *ᵥ c)`; Sⁿ₊ is
`Matrix.PosSemidef`. -/
theorem corollary_5 {n : ℕ} (a b c : Fin n → ℝ) :
    IsROG {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef ∧ 0 ≤ a ⬝ᵥ (X *ᵥ c) ∧
      0 ≤ b ⬝ᵥ (X *ᵥ c)} := by sorry

end ROGCones
