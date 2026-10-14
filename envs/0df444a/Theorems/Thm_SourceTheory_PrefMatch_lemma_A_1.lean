-- Prove2me | Theorems.Thm_SourceTheory_PrefMatch_lemma_A_1
-- name    : SourceTheory.PrefMatch.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:17.238735+00:00
-- url     : https://prove2.me/theorems/cb0d3a2c-9b4b-47d9-bf51-d7f1d8a93e9d
-- title:
--   Lemma A.1, p. 8779 — source preference (6) is equivalent to its weak-premise form (7)
-- statement:
--   Assume structural Assumption 1, and let $\mathcal C$ and $\mathcal A$ be sources. Then $\mathcal C$ is preferred to $\mathcal A$ in the sense of Definition 2, i.e. for all twofold partitions $(C_1, C_2)$ from $\mathcal C$ and $(A_1, A_2)$ from $\mathcal A$
--
--   $$W(A_1) = W(C_1) \implies W(A_2) \le W(C_2), \tag{6}$$
--
--   if and only if for all such partitions
--
--   $$W(A_1) \ge W(C_1) \implies W(A_2) \le W(C_2). \tag{7}$$
--
--   The weak-premise form (7) is easier to test empirically, since exact indifferences need not be elicited (Appendix A of the paper).
--
--   **Formalization Note.** Twofold partitions are $(C_1, C_1^c)$ and $(A_1, A_1^c)$.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Lemma A.1, p. 8779 (Equations (6), p. 8771, and (7), p. 8772)

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.PrefMatch

open Set SourceTheory.Uniform

/-- Lemma A.1 (p. 8779): source preference (6) for `𝒞` over `𝒜` (premise `W(A₁) = W(C₁)`) is
equivalent to (7) (p. 8772), the same condition with the weak premise `W(A₁) ≥ W(C₁)`. -/
theorem lemma_A_1 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (h𝒞 : IsSource 𝓔 W 𝒞) :
    IsPreferredTo W 𝒞 𝒜 ↔ ∀ C₁ ∈ 𝒞, ∀ A₁ ∈ 𝒜, W C₁ ≤ W A₁ → W (A₁ᶜ) ≤ W (C₁ᶜ) := by sorry

end SourceTheory.PrefMatch
