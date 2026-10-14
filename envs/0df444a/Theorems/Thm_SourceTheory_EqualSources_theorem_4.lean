-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_theorem_4
-- name    : SourceTheory.EqualSources.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:16.15063+00:00
-- url     : https://prove2.me/theorems/25184fce-f9da-4a8e-892d-56965308bc63
-- title:
--   Theorem 4, p. 8775 — two sources are equally preferred and insensitive with a regular region iff both are uniform with w_A = w_C; the region can then be [∅, S]
-- statement:
--   Let $\succcurlyeq$, $U$ and $W$ satisfy structural Assumption 1 on the events $\mathcal E$, and let $\mathcal A$ and $\mathcal C$ be sources. Then:
--
--   1. The following are equivalent.
--      - There are events $B, D \in \mathcal E$ such that $[B, D]$ is a regular insensitivity region for $\mathcal A$ and for $\mathcal C$, $\mathcal A$ and $\mathcal C$ are **equally preferred** ($\mathcal C$ is preferred to $\mathcal A$ and $\mathcal A$ is preferred to $\mathcal C$, Definition 2), and $\mathcal A$ and $\mathcal C$ are **equally insensitive** with region $[B, D]$ (each is more insensitive than the other with region $[B, D]$, Definition 4).
--      - Both sources are uniform, with a-neutral probability measures $P_{\mathcal A}$ and $P_{\mathcal C}$, and they have the same source function $w$:
--      $$W = w \circ P_{\mathcal A} \text{ on } \mathcal A, \qquad W = w \circ P_{\mathcal C} \text{ on } \mathcal C.$$
--   2. If both sources are uniform with the same source function, then $\mathcal A$ and $\mathcal C$ are equally insensitive with the maximal insensitivity region $[\emptyset, S]$.
--
--   Assumption 2 is not imposed: it follows from the other conditions. The theorem shows that two sources can be at the same level of ambiguity attitude, in both components, only if both are uniform, and that they then have the same source function.
--
--   **Formalization Note.** The paper does not say for which source the region is regular; it is read as regular for both $\mathcal A$ and $\mathcal C$, as the proof applies Theorem 1 to each source with the same region. "$w_{\mathcal A} = w_{\mathcal C}$" is encoded as a single continuous probability weighting function $w$ that is the source function of both sources. The boundary events $B, D$ are events, not necessarily from either source.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Theorem 4, p. 8775 (proof p. 8780)

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- Theorem 4 (Baillon et al. 2025, p. 8775). Under structural Assumption 1, sources `𝒜` and `𝒞` are
equally preferred and equally insensitive with an insensitivity region `[B, D]` that is regular (for
both sources) if and only if both are uniform and `w_𝒜 = w_𝒞` (one function `w` is a source function of
both). They are then equally insensitive with the maximal insensitivity region `[∅, S]`. -/
theorem theorem_4 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞) :
    ((∃ B ∈ 𝓔, ∃ D ∈ 𝓔, SourceTheory.Uniform.IsRegularRegion W 𝒜 B D ∧ SourceTheory.Uniform.IsRegularRegion W 𝒞 B D ∧
        SourceTheory.Uniform.IsPreferredTo W 𝒞 𝒜 ∧ SourceTheory.Uniform.IsPreferredTo W 𝒜 𝒞 ∧
        SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 B D ∧ SourceTheory.Uniform.IsMoreInsensitive W 𝒞 𝒜 B D) ↔
      ∃ (PA PC : Set S → ℝ) (w : ℝ → ℝ), SourceTheory.Uniform.IsUniformWith pref U 𝒜 PA ∧ SourceTheory.Uniform.IsUniformWith pref U 𝒞 PC ∧
        SourceTheory.Uniform.IsSourceFunction W 𝒜 PA w ∧ SourceTheory.Uniform.IsSourceFunction W 𝒞 PC w) ∧
    ((∃ (PA PC : Set S → ℝ) (w : ℝ → ℝ), SourceTheory.Uniform.IsUniformWith pref U 𝒜 PA ∧ SourceTheory.Uniform.IsUniformWith pref U 𝒞 PC ∧
        SourceTheory.Uniform.IsSourceFunction W 𝒜 PA w ∧ SourceTheory.Uniform.IsSourceFunction W 𝒞 PC w) →
      SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 ∅ univ ∧ SourceTheory.Uniform.IsMoreInsensitive W 𝒞 𝒜 ∅ univ) := by sorry

end SourceTheory.EqualSources
