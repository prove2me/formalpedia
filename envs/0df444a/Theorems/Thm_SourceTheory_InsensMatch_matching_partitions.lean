-- Prove2me | Theorems.Thm_SourceTheory_InsensMatch_matching_partitions
-- name    : SourceTheory.InsensMatch.matching_partitions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:16.891302+00:00
-- url     : https://prove2.me/theorems/56369469-49f3-488d-bd21-f6d58dbda287
-- title:
--   Proof of Theorem 3, p. 8780 — (C₁,C₂,C₃) matches (A₁,A₂,A₃) iff φ(q₁) = p₁ and φ(q₁+q₂) = p₁+p₂
-- statement:
--   Assume structural Assumption 1 and Assumption 2 for sources $\mathcal C$ and $\mathcal A$, and let $\varphi$ be the pmatcher from $\mathcal A$ to $\mathcal C$ (a transformation with $w_{\mathcal A} = w_{\mathcal C} \circ \varphi$ on $[0,1]$). Let $(C_1, C_2, C_3)$ be a threefold partition of $S$ from $\mathcal C$ and $(A_1, A_2, A_3)$ one from $\mathcal A$, with a-neutral probabilities $p_i = P_{\mathcal C}(C_i)$ and $q_i = P_{\mathcal A}(A_i)$. The partitions are *matching* ($A_1 \sim C_1$ and $A_3^c \sim C_3^c$) if and only if
--
--   $$\varphi(q_1) = p_1 \quad\text{and}\quad \varphi(q_1 + q_2) = p_1 + p_2.$$
--
--   This is the first step of the paper's proof of Theorem 3: it rewrites the premise of Definition 4's conditions (8)–(9) as two values of the pmatcher.
--
--   **Formalization Note.** Matching is written with $W$: $W(A_1) = W(C_1)$ and $W(A_3^c) = W(C_3^c)$. Partitions may have empty cells.
-- source:
--   Baillon et al. (2025), Management Science 71(10), proof of Theorem 3, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.InsensMatch

open Set

/-- Proof of Theorem 3 (p. 8780), first step: threefold partitions `(C₁, C₂, C₃)` from `𝒞` and
`(A₁, A₂, A₃)` from `𝒜` are matching (`A₁ ~ C₁` and `A₃ᶜ ~ C₃ᶜ`) iff `φ(q₁) = p₁` and
`φ(q₁ + q₂) = p₁ + p₂`, where `qᵢ = P_𝒜(Aᵢ)` and `pᵢ = P_𝒞(Cᵢ)`. -/
theorem matching_partitions {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (φ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p))
    (C₁ C₂ C₃ A₁ A₂ A₃ : Set S) (hC : SourceTheory.Uniform.IsPartition3 𝒞 C₁ C₂ C₃) (hA : SourceTheory.Uniform.IsPartition3 𝒜 A₁ A₂ A₃) :
    (W A₁ = W C₁ ∧ W (A₃ᶜ) = W (C₃ᶜ)) ↔
      (φ (PA A₁) = PC C₁ ∧ φ (PA A₁ + PA A₂) = PC C₁ + PC C₂) := by sorry

end SourceTheory.InsensMatch
