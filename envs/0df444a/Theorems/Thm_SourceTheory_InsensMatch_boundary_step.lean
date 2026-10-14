-- Prove2me | Theorems.Thm_SourceTheory_InsensMatch_boundary_step
-- name    : SourceTheory.InsensMatch.boundary_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:18.958978+00:00
-- url     : https://prove2.me/theorems/4cc8beb2-aac2-49c5-991c-4245dddd7147
-- title:
--   Proof of Theorem 3, p. 8780 — for D from A, the boundary condition A₃ᶜ ≼ D means q₁ + q₂ ≤ P_A(D)
-- statement:
--   Assume structural Assumption 1. Let $\mathcal A$ be a source that is uniform with a-neutral probability $P_{\mathcal A}$ and source function $w_{\mathcal A}$. Let $D \in \mathcal A$, and let $(A_1, A_2, A_3)$ be a threefold partition of $S$ from $\mathcal A$ with $q_i = P_{\mathcal A}(A_i)$. Then
--
--   $$A_3^c \preccurlyeq D \iff q_1 + q_2 \le P_{\mathcal A}(D).$$
--
--   In the proof of Theorem 3 this identifies the upper bound of $\varphi$'s insensitivity region: the boundary condition of (8) becomes the condition $p_1 + p_2 \le d$ of (13) with $d = P_{\mathcal A}(D)$, because the $q$ probabilities are the arguments of $\varphi$.
--
--   **Formalization Note.** $A_3^c \preccurlyeq D$ is $W(A_3^c) \le W(D)$. The statement involves only the source $\mathcal A$, so the second source and Assumption 2 are not assumed.
-- source:
--   Baillon et al. (2025), Management Science 71(10), proof of Theorem 3, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.InsensMatch

open Set

/-- Proof of Theorem 3 (p. 8780), boundary step: for `D` from `𝒜` and a threefold partition
`(A₁, A₂, A₃)` from `𝒜`, `A₃ᶜ ≼ D` iff `q₁ + q₂ ≤ P_𝒜(D)`, where `qᵢ = P_𝒜(Aᵢ)`. -/
theorem boundary_step {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (PA : Set S → ℝ) (wA : ℝ → ℝ)
    (hPA : SourceTheory.Uniform.IsUniformWith pref U 𝒜 PA) (hwA : SourceTheory.Uniform.IsSourceFunction W 𝒜 PA wA)
    (D : Set S) (hD : D ∈ 𝒜) (A₁ A₂ A₃ : Set S) (hA : SourceTheory.Uniform.IsPartition3 𝒜 A₁ A₂ A₃) :
    W (A₃ᶜ) ≤ W D ↔ PA A₁ + PA A₂ ≤ PA D := by sorry

end SourceTheory.InsensMatch
