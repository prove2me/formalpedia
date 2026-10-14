-- Prove2me | Theorems.Thm_SourceTheory_PrefMatch_theorem_2_matching_step
-- name    : SourceTheory.PrefMatch.theorem_2_matching_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:09.72195+00:00
-- url     : https://prove2.me/theorems/941339ab-2bec-45a6-a1bd-6e3306ee844f
-- title:
--   Proof of Theorem 2, p. 8780 — for matching (C₁,C₂), (A₁,A₂): φ(q₁) = p₁, and A₂ ≼ C₂ iff φ(q₂) ≤ 1 − φ(1 − q₂)
-- statement:
--   Assume structural Assumption 1 and Assumption 2 for sources $\mathcal C$ and $\mathcal A$, and let $\varphi$ be a transformation with $w_{\mathcal A} = w_{\mathcal C} \circ \varphi$ on $[0,1]$. Let $(C_1, C_2)$ be a twofold partition from $\mathcal C$ and $(A_1, A_2)$ one from $\mathcal A$ that are *matching*, $W(A_1) = W(C_1)$, with a-neutral probabilities $p_i = P_{\mathcal C}(C_i)$ and $q_i = P_{\mathcal A}(A_i)$. Then $\varphi(q_1) = p_1$, and
--
--   $$A_2 \preccurlyeq C_2 \iff \varphi(q_2) \le 1 - \varphi(1 - q_2).$$
--
--   This is the computation in the proof of Theorem 2: since $p_2 = 1 - p_1 = 1 - \varphi(q_1) = 1 - \varphi(1-q_2)$, the conclusion of source preference (6) at a matching pair is the dislike inequality of $\varphi$ at $q_2$.
--
--   **Formalization Note.** Twofold partitions are $(C_1, C_1^c)$ and $(A_1, A_1^c)$, so $q_2 = P_{\mathcal A}(A_1^c)$; $A_2 \preccurlyeq C_2$ is $W(A_1^c) \le W(C_1^c)$.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 2, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.PrefMatch

open Set SourceTheory.Uniform

/-- Proof of Theorem 2 (p. 8780): for matching twofold partitions `(C₁, C₂)` from `𝒞` and
`(A₁, A₂)` from `𝒜` (`C₂ = C₁ᶜ`, `A₂ = A₁ᶜ`), `φ(q₁) = p₁`, and `A₂ ≼ C₂` is equivalent to
`φ(q₂) ≤ 1 − φ(1 − q₂)`, where `pᵢ = P_𝒞(Cᵢ)` and `qᵢ = P_𝒜(Aᵢ)`. -/
theorem theorem_2_matching_step {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞)
    (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) (h2 : Assumption2 pref U W 𝒞 𝒜 PC PA wC wA)
    (φ : ℝ → ℝ) (hφ : IsTransformation φ) (hφA : ∀ p ∈ Icc (0 : ℝ) 1, wA p = wC (φ p)) :
    ∀ C₁ ∈ 𝒞, ∀ A₁ ∈ 𝒜, W A₁ = W C₁ →
      φ (PA A₁) = PC C₁ ∧ (W (A₁ᶜ) ≤ W (C₁ᶜ) ↔ φ (PA (A₁ᶜ)) ≤ 1 - φ (1 - PA (A₁ᶜ))) := by sorry

end SourceTheory.PrefMatch
