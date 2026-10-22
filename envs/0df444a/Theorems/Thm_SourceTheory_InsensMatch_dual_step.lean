-- Prove2me | Theorems.Thm_SourceTheory_InsensMatch_dual_step
-- name    : SourceTheory.InsensMatch.dual_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:26.787063+00:00
-- url     : https://prove2.me/theorems/c6f79c4c-3529-434c-b11f-752d7b96bcf8
-- title:
--   Proof of Theorem 3, p. 8780 — the dual case (9)/(14): A₂ᶜ ≼ C₂ᶜ iff φ(q₁+q₂) − φ(q₁) ≤ 1 − φ(q₁+q₃), and B ≼ A₁ iff P_A(B) ≤ q₁
-- statement:
--   Assume structural Assumption 1 and Assumption 2 for sources $\mathcal C$ and $\mathcal A$, and let $\varphi$ be the pmatcher from $\mathcal A$ to $\mathcal C$. Let $(C_1, C_2, C_3)$ and $(A_1, A_2, A_3)$ be matching threefold partitions of $S$ from $\mathcal C$ and $\mathcal A$ ($W(A_1) = W(C_1)$, $W(A_3^c) = W(C_3^c)$), with $q_i = P_{\mathcal A}(A_i)$, and let $B \in \mathcal A$. Then
--
--   $$A_2^c \preccurlyeq C_2^c \iff \varphi(q_1 + q_2) - \varphi(q_1) \le 1 - \varphi(q_1 + q_3) \qquad\text{and}\qquad B \preccurlyeq A_1 \iff P_{\mathcal A}(B) \le q_1.$$
--
--   These are the two translations behind the paper's remark that "Equations (9) and (14) are similar": the conclusion of (9) becomes the inequality of (14), and the boundary condition of (9) becomes $p_1 \ge b$ with $b = P_{\mathcal A}(B)$.
--
--   **Formalization Note.** $A_2^c \preccurlyeq C_2^c$ is $W(A_2^c) \le W(C_2^c)$, and $B \preccurlyeq A_1$ is $W(B) \le W(A_1)$. The paper states this step in one sentence; the two clauses spell out its two halves, mirroring the weight comparison and the boundary step for (8)/(13).
-- source:
--   Baillon et al. (2025), Management Science 71(10), proof of Theorem 3, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.InsensMatch

open Set

/-- Proof of Theorem 3 (p. 8780), the dual case (9)/(14): for matching threefold partitions,
`A₂ᶜ ≼ C₂ᶜ` iff `φ(q₁ + q₂) − φ(q₁) ≤ 1 − φ(q₁ + q₃)`, and for `B` from `𝒜`, `B ≼ A₁` iff
`P_𝒜(B) ≤ q₁`, where `qᵢ = P_𝒜(Aᵢ)`. -/
theorem dual_step {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : SourceTheory.Uniform.Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (φ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p))
    (C₁ C₂ C₃ A₁ A₂ A₃ : Set S) (hC : SourceTheory.Uniform.IsPartition3 𝒞 C₁ C₂ C₃) (hA : SourceTheory.Uniform.IsPartition3 𝒜 A₁ A₂ A₃)
    (hm₁ : W A₁ = W C₁) (hm₃ : W (A₃ᶜ) = W (C₃ᶜ)) (B : Set S) (hB : B ∈ 𝒜) :
    (W (A₂ᶜ) ≤ W (C₂ᶜ) ↔ φ (PA A₁ + PA A₂) - φ (PA A₁) ≤ 1 - φ (PA A₁ + PA A₃)) ∧
      (W B ≤ W A₁ ↔ PA B ≤ PA A₁) := by sorry

end SourceTheory.InsensMatch
