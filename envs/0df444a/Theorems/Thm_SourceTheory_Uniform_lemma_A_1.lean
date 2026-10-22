-- Prove2me | Theorems.Thm_SourceTheory_Uniform_lemma_A_1
-- name    : SourceTheory.Uniform.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:57.269973+00:00
-- url     : https://prove2.me/theorems/bb08f99d-bca7-4732-a2d2-5df751cc46d0
-- title:
--   Lemma A.1, p. 8779 — source preference (6) is equivalent to its weak-premise form (7)
-- statement:
--   Work under structural Assumption 1 and let $\mathcal A$, $\mathcal C$ be sources. Source preference for $\mathcal C$ over $\mathcal A$ (Definition 2, Equation (6)),
--   $$W(A_1)=W(C_1)\ \Longrightarrow\ W(A_2)\le W(C_2)\quad\text{for all twofold partitions } (C_1,C_2) \text{ from } \mathcal C,\ (A_1,A_2) \text{ from } \mathcal A,$$
--   holds if and only if Equation (7) holds:
--   $$W(A_1)\ge W(C_1)\ \Longrightarrow\ W(A_2)\le W(C_2)\quad\text{for all such partitions}.$$
--   Here $A_2 = A_1^c$ and $C_2 = C_1^c$.
--
--   The weak-premise form (7) is the version used throughout the proof of Theorem 1.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Lemma A.1, p. 8779; Equations (6), (7), pp. 8771–8772

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set

/-- Lemma A.1 (p. 8779): source preference (6) for `𝒞` over `𝒜` (premise `W(A₁) = W(C₁)`) is
equivalent to (7) (p. 8772), the same condition with the weak premise `W(A₁) ≥ W(C₁)`. -/
theorem lemma_A_1 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞) :
    IsPreferredTo W 𝒞 𝒜 ↔ ∀ C₁ ∈ 𝒞, ∀ A₁ ∈ 𝒜, W C₁ ≤ W A₁ → W (A₁ᶜ) ≤ W (C₁ᶜ) := by sorry

end SourceTheory.Uniform
