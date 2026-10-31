-- Prove2me | Theorems.Thm_ROGCones_theorem_5
-- name    : ROGCones.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:13.046708+00:00
-- url     : https://prove2.me/theorems/a8032d57-9eac-462e-8be2-058b84ea3cfa
-- title:
--   Theorem 5 (Dines) — without a nontrivial PSD combination, $x \mapsto (x^\top M_1x, x^\top M_2x)$ is onto $\mathbb R^2$
-- statement:
--   Let $M_1, M_2 \in \mathbb S^n$ and suppose that $\alpha_1 M_1 + \alpha_2 M_2 \notin \mathbb S^n_+$ for all $(\alpha_1, \alpha_2) \neq (0,0)$. Then
--   $$
--   \{(x^\top M_1 x,\ x^\top M_2 x) \in \mathbb R^2 : x \in \mathbb R^n\} = \mathbb R^2 ,
--   $$
--   i.e. for every $y \in \mathbb R^2$ there is $x \in \mathbb R^n$ with $x^\top M_1 x = y_1$ and $x^\top M_2 x = y_2$. This is a convexity theorem of Dines on the joint image of two quadratic forms, used in the proofs of Propositions 3 and 4.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: {(xᵀM₁x, xᵀM₂x) ∈ ℝ² : x ∈ ℝⁿ} = ℝ² → Set.range (fun x => (x ⬝ᵥ (M₁ *ᵥ x), x ⬝ᵥ (M₂ *ᵥ x))) = Set.univ in ℝ × ℝ; reason: same set equality
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Theorem 5 (Dines [13]), p.17

import Mathlib

open Matrix

namespace ROGCones

/-- **Theorem 5 (Dines [13]) — without a nontrivial PSD combination, the joint image of two
quadratic forms is the whole plane.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Theorem 5 (Dines [13]), p.17: "Let M₁, M₂ ∈ Sⁿ
and suppose that for all (α₁, α₂) ≠ (0, 0), we have α₁M₁+α₂M₂ ∉ Sⁿ₊. Then,
{(x⊤M₁x, x⊤M₂x) ∈ ℝ² : x ∈ ℝⁿ} = ℝ², i.e., for every y ∈ ℝ², there exists an x ∈ ℝⁿ such that
x⊤M₁x = y₁ and x⊤M₂x = y₂."

**Formalization Note.** ℝⁿ is `Fin n → ℝ`, ℝ² is `ℝ × ℝ`, `xᵀMx` is `x ⬝ᵥ (M *ᵥ x)`, Sⁿ₊ is
`Matrix.PosSemidef`. The conclusion is the set equality, stated as `Set.range … = Set.univ`. -/
theorem theorem_5 {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ) (hM₁ : M₁.IsSymm) (hM₂ : M₂.IsSymm)
    (h : ∀ α₁ α₂ : ℝ, (α₁, α₂) ≠ (0, 0) → ¬ (α₁ • M₁ + α₂ • M₂).PosSemidef) :
    Set.range (fun x : Fin n → ℝ => (x ⬝ᵥ (M₁ *ᵥ x), x ⬝ᵥ (M₂ *ᵥ x))) = Set.univ := by sorry

end ROGCones
