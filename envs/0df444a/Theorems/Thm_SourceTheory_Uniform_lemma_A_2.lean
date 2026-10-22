-- Prove2me | Theorems.Thm_SourceTheory_Uniform_lemma_A_2
-- name    : SourceTheory.Uniform.lemma_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:56.662136+00:00
-- url     : https://prove2.me/theorems/7daf89b5-cb69-4888-88fd-5721787cdb6c
-- title:
--   Lemma A.2, p. 8779 — (8) ⇔ (A.1) and (9) ⇔ (A.2): insensitivity with weak premises
-- statement:
--   Work under structural Assumption 1, let $\mathcal A$, $\mathcal C$ be sources and $B$, $D$ arbitrary sets. All quantifiers below range over ordered threefold partitions $(C_1,C_2,C_3)$ of $S$ from $\mathcal C$ and $(A_1,A_2,A_3)$ from $\mathcal A$.
--
--   1. Equation (8), $W(A_1)=W(C_1)\ \&\ W(A_3^c)=W(C_3^c)\le W(D)\Rightarrow W(A_2)\ge W(C_2)$, holds for all such partitions if and only if
--   $$W(C_1)\ge W(A_1)\ \&\ W(C_3^c)\le W(A_3^c)\le W(D)\ \Longrightarrow\ W(A_2)\ge W(C_2) \quad (A.1)$$
--   holds for all such partitions.
--   2. Equation (9), $W(B)\le W(A_1)=W(C_1)\ \&\ W(A_3^c)=W(C_3^c)\Rightarrow W(A_2^c)\le W(C_2^c)$, holds for all such partitions if and only if
--   $$W(C_3^c)\le W(A_3^c)\ \&\ W(C_1)\ge W(A_1)\ge W(B)\ \Longrightarrow\ W(A_2^c)\le W(C_2^c) \quad (A.2)$$
--   holds for all such partitions.
--
--   Together, $\mathcal A$ is more insensitive than $\mathcal C$ with region $[B,D]$ (Definition 4) exactly when (A.1) and (A.2) hold. These weak-premise forms are the ones used in the proof of Theorem 1.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Lemma A.2, (A.1), (A.2), p. 8779; Equations (8), (9), p. 8772

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set

/-- Lemma A.2 (p. 8779): over all threefold partitions `(C₁, C₂, C₃)` from `𝒞` and
`(A₁, A₂, A₃)` from `𝒜`, Equation (8) is equivalent to (A.1), and Equation (9) is equivalent
to (A.2). -/
theorem lemma_A_2 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞) (B D : Set S) :
    ((∀ C₁ C₂ C₃ A₁ A₂ A₃ : Set S, IsPartition3 𝒞 C₁ C₂ C₃ → IsPartition3 𝒜 A₁ A₂ A₃ →
        W A₁ = W C₁ → W (A₃ᶜ) = W (C₃ᶜ) → W (C₃ᶜ) ≤ W D → W C₂ ≤ W A₂) ↔
      (∀ C₁ C₂ C₃ A₁ A₂ A₃ : Set S, IsPartition3 𝒞 C₁ C₂ C₃ → IsPartition3 𝒜 A₁ A₂ A₃ →
        W A₁ ≤ W C₁ → W (C₃ᶜ) ≤ W (A₃ᶜ) → W (A₃ᶜ) ≤ W D → W C₂ ≤ W A₂)) ∧
    ((∀ C₁ C₂ C₃ A₁ A₂ A₃ : Set S, IsPartition3 𝒞 C₁ C₂ C₃ → IsPartition3 𝒜 A₁ A₂ A₃ →
        W B ≤ W A₁ → W A₁ = W C₁ → W (A₃ᶜ) = W (C₃ᶜ) → W (A₂ᶜ) ≤ W (C₂ᶜ)) ↔
      (∀ C₁ C₂ C₃ A₁ A₂ A₃ : Set S, IsPartition3 𝒞 C₁ C₂ C₃ → IsPartition3 𝒜 A₁ A₂ A₃ →
        W (C₃ᶜ) ≤ W (A₃ᶜ) → W A₁ ≤ W C₁ → W B ≤ W A₁ → W (A₂ᶜ) ≤ W (C₂ᶜ))) := by sorry

end SourceTheory.Uniform
