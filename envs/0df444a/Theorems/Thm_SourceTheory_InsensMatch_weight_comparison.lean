-- Prove2me | Theorems.Thm_SourceTheory_InsensMatch_weight_comparison
-- name    : SourceTheory.InsensMatch.weight_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:15.218984+00:00
-- url     : https://prove2.me/theorems/2a916f77-29d1-4e03-9bfe-f87071728459
-- title:
--   Proof of Theorem 3, p. 8780 — for matching partitions, A₂ ≽ C₂ iff φ(q₂) ≥ φ(q₁+q₂) − φ(q₁)
-- statement:
--   Assume structural Assumption 1 and Assumption 2 for sources $\mathcal C$ and $\mathcal A$, and let $\varphi$ be the pmatcher from $\mathcal A$ to $\mathcal C$. Let $(C_1, C_2, C_3)$ and $(A_1, A_2, A_3)$ be threefold partitions of $S$ from $\mathcal C$ and $\mathcal A$ that are matching, $W(A_1) = W(C_1)$ and $W(A_3^c) = W(C_3^c)$, and write $q_i = P_{\mathcal A}(A_i)$. Then
--
--   $$A_2 \succcurlyeq C_2 \iff \varphi(q_2) \ge \varphi(q_1 + q_2) - \varphi(q_1).$$
--
--   This is the step of the proof of Theorem 3 that turns the conclusion of condition (8) into the inequality of condition (13) for $\varphi$.
--
--   **Formalization Note.** $A_2 \succcurlyeq C_2$ is $W(C_2) \le W(A_2)$.
-- source:
--   Baillon et al. (2025), Management Science 71(10), proof of Theorem 3, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.InsensMatch

open Set

/-- Proof of Theorem 3 (p. 8780), second step: for matching threefold partitions,
`A₂ ≽ C₂` iff `φ(q₂) ≥ φ(q₁ + q₂) − φ(q₁)`, where `qᵢ = P_𝒜(Aᵢ)`. -/
theorem weight_comparison {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (φ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p))
    (C₁ C₂ C₃ A₁ A₂ A₃ : Set S) (hC : SourceTheory.Uniform.IsPartition3 𝒞 C₁ C₂ C₃) (hA : SourceTheory.Uniform.IsPartition3 𝒜 A₁ A₂ A₃)
    (hm₁ : W A₁ = W C₁) (hm₃ : W (A₃ᶜ) = W (C₃ᶜ)) :
    W C₂ ≤ W A₂ ↔ φ (PA A₁ + PA A₂) - φ (PA A₁) ≤ φ (PA A₂) := by sorry

end SourceTheory.InsensMatch
