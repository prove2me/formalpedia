-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_observation_3
-- name    : SourceTheory.EqualSources.observation_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:23.79811+00:00
-- url     : https://prove2.me/theorems/212b02e6-7c1d-4e04-9b14-8147973f2f60
-- title:
--   Observation 3, p. 8774 — source preference and source insensitivity are transitive; the new insensitivity region is the intersection
-- statement:
--   Let $\succcurlyeq$, $U$ and $W$ satisfy structural Assumption 1 on the events $\mathcal E$, and let $\mathcal A$, $\mathcal S$ and $\mathcal C$ be sources.
--
--   1. **Source preference is transitive.** If $\mathcal S$ is preferred to $\mathcal A$ and $\mathcal C$ is preferred to $\mathcal S$ (Definition 2), then $\mathcal C$ is preferred to $\mathcal A$.
--   2. **Source insensitivity is transitive.** Let $B_1, D_1, B_2, D_2 \in \mathcal E$. If $\mathcal A$ is more insensitive than $\mathcal S$ with region $[B_1, D_1]$ and $\mathcal S$ is more insensitive than $\mathcal C$ with region $[B_2, D_2]$, then for all events $B, D \in \mathcal E$ with
--   $$W(B) \ge W(B_1),\quad W(B) \ge W(B_2),\quad W(D) \le W(D_1),\quad W(D) \le W(D_2),$$
--   $\mathcal A$ is more insensitive than $\mathcal C$ with region $[B, D]$.
--
--   The region $[B, D]$ in part 2 is any region inside the intersection of $[B_1, D_1]$ and $[B_2, D_2]$ in the event order. The observation lets a chain of comparisons between sources be collapsed into one comparison, which the proof of Theorem 4 uses to compare each source with itself.
--
--   **Formalization Note.** Event preference is $W$-order, so "$B \succcurlyeq B_1$" is $W(B) \ge W(B_1)$. The paper's middle source is called $\mathcal B$; here it is $\mathcal S$, to avoid a clash with the boundary event $B$.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Observation 3, p. 8774 (proof p. 8779)

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- Observation 3 (p. 8774): source preference and source insensitivity are transitive; for
insensitivity the new region is the intersection of the other two (any `[B, D]` with `B ≽ B₁, B₂` and
`D ≼ D₁, D₂`). The middle source is written `𝒮`. -/
theorem observation_3 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒮 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒮 : SourceTheory.Uniform.IsSource 𝓔 W 𝒮)
    (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞) :
    (SourceTheory.Uniform.IsPreferredTo W 𝒮 𝒜 → SourceTheory.Uniform.IsPreferredTo W 𝒞 𝒮 → SourceTheory.Uniform.IsPreferredTo W 𝒞 𝒜) ∧
    (∀ B₁ ∈ 𝓔, ∀ D₁ ∈ 𝓔, ∀ B₂ ∈ 𝓔, ∀ D₂ ∈ 𝓔,
      SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒮 B₁ D₁ → SourceTheory.Uniform.IsMoreInsensitive W 𝒮 𝒞 B₂ D₂ →
      ∀ B ∈ 𝓔, ∀ D ∈ 𝓔, W B₁ ≤ W B → W B₂ ≤ W B → W D ≤ W D₁ → W D ≤ W D₂ →
        SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 B D) := by sorry

end SourceTheory.EqualSources
