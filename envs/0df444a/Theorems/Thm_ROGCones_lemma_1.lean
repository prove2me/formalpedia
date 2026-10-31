-- Prove2me | Theorems.Thm_ROGCones_lemma_1
-- name    : ROGCones.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:29.293767+00:00
-- url     : https://prove2.me/theorems/fd66d289-c736-4c21-ad5f-e3386f9ccb4f
-- title:
--   Lemma 1 — a closed convex cone in $\mathbb S^n_+$ is ROG iff all its extreme rays have rank one
-- statement:
--   Let $S \subseteq \mathbb S^n_+$ be a closed convex cone. Then
--   $$
--   S \text{ is ROG} \iff \operatorname{rank}(X) = 1 \text{ for every extreme ray } \mathbb R_+X \text{ of } S .
--   $$
--   This turns rank-one generation into a statement about extreme rays, and is the basic tool for showing that a cone is, or is not, ROG.
--
--   **Formalization Note** "Closed convex cone in $\mathbb S^n_+$" is five hypotheses: the set is nonempty, every element is positive semidefinite, the set is closed and convex, and it is closed under multiplication by nonnegative scalars.
--
--   Differences from the source:
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨M, X⟩, xᵀMx, xxᵀ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (M * X).trace, x ⬝ᵥ (M *ᵥ x), vecMulVec x x; reason: standard Lean conventions; tr(MX) = Σᵢⱼ MᵢⱼXᵢⱼ for symmetric M, X; same instances
--   - encoding: ROG defined for a closed convex cone in 𝕊ⁿ₊ (Definition 1) → IsROG, a predicate on any set of matrices; reason: every set it is applied to here is a closed convex cone in 𝕊ⁿ₊, where the two notions coincide
--   - encoding: S ⊆ 𝕊ⁿ₊ a closed convex cone → hypotheses hS_ne, hS_psd, hS_closed, hS_convex, hS_cone (closed under t • X, t ≥ 0); reason: these are the defining properties; same instances
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Lemma 1, p.6

import Mathlib
import Definitions.Def_ROGCones_IsROG
import Definitions.Def_ROGCones_IsExtremeRay

namespace ROGCones

/-- **Lemma 1 — a closed convex cone in Sⁿ₊ is ROG iff all its extreme rays have rank one.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Lemma 1, p.6: "Let S ⊆ Sⁿ₊ be a closed convex
cone. Then, S is ROG if and only if for each extreme ray ℝ₊X of S we have rank(X) = 1."

**Formalization Note.** "S ⊆ Sⁿ₊ is a closed convex cone" is the five hypotheses `hS_ne`,
`hS_psd`, `hS_closed`, `hS_convex`, `hS_cone` (closed under nonnegative scaling). `ℝ₊X` is an
extreme ray of `S` is `IsExtremeRay S X` (which includes `X ≠ 0` and `X ∈ S`). -/
theorem lemma_1 {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℝ))
    (hS_ne : S.Nonempty) (hS_psd : ∀ X ∈ S, X.PosSemidef) (hS_closed : IsClosed S)
    (hS_convex : Convex ℝ S)
    (hS_cone : ∀ X ∈ S, ∀ t : ℝ, 0 ≤ t → t • X ∈ S) :
    IsROG S ↔ ∀ X : Matrix (Fin n) (Fin n) ℝ, IsExtremeRay S X → X.rank = 1 := by sorry

end ROGCones
