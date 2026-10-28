-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_reversed_implication
-- name    : SourceTheory.EqualSources.reversed_implication
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:07.794398+00:00
-- url     : https://prove2.me/theorems/02bf869f-f972-4334-8358-7cbb69670b2b
-- title:
--   Proof of Theorem 4, p. 8780 — the reversed implication: uniform sources with a common source function are equally preferred and insensitive with a regular region
-- statement:
--   Let $\succcurlyeq$, $U$ and $W$ satisfy structural Assumption 1 on the events $\mathcal E$, and let $\mathcal A$ and $\mathcal C$ be sources. Suppose both sources are uniform, with a-neutral probability measures $P_{\mathcal A}$ and $P_{\mathcal C}$, and that a single continuous probability weighting function $w$ is the source function of both:
--
--   $$W = w \circ P_{\mathcal A} \text{ on } \mathcal A, \qquad W = w \circ P_{\mathcal C} \text{ on } \mathcal C.$$
--
--   Then there are events $B, D \in \mathcal E$ such that
--   1. the insensitivity region $[B, D]$ is regular for $\mathcal A$ and for $\mathcal C$;
--   2. $\mathcal C$ is preferred to $\mathcal A$ and $\mathcal A$ is preferred to $\mathcal C$ (Definition 2);
--   3. $\mathcal A$ is more insensitive than $\mathcal C$ and $\mathcal C$ is more insensitive than $\mathcal A$, both with region $[B, D]$ (Definition 4).
--
--   This is the "if" direction of Theorem 4, which the paper calls direct.
--
--   **Formalization Note.** "Equally preferred" and "equally insensitive" are the comparative relations in both directions (p. 8774). "$w_{\mathcal A} = w_{\mathcal C}$" is encoded as one function $w$ that is a source function of both sources.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 4, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- Proof of Theorem 4, p. 8780: "(The reversed implication is direct.)" If `𝒜` and `𝒞` are uniform
and one continuous probability weighting function `w` is the source function of both, then they are
equally preferred and equally insensitive with an insensitivity region that is regular for both. -/
theorem reversed_implication {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 𝒞 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (h𝒞 : SourceTheory.Uniform.IsSource 𝓔 W 𝒞)
    (PA PC : Set S → ℝ) (w : ℝ → ℝ)
    (hA : SourceTheory.Uniform.IsUniformWith pref U 𝒜 PA) (hC : SourceTheory.Uniform.IsUniformWith pref U 𝒞 PC)
    (hwA : SourceTheory.Uniform.IsSourceFunction W 𝒜 PA w) (hwC : SourceTheory.Uniform.IsSourceFunction W 𝒞 PC w) :
    ∃ B ∈ 𝓔, ∃ D ∈ 𝓔, SourceTheory.Uniform.IsRegularRegion W 𝒜 B D ∧ SourceTheory.Uniform.IsRegularRegion W 𝒞 B D ∧
      SourceTheory.Uniform.IsPreferredTo W 𝒞 𝒜 ∧ SourceTheory.Uniform.IsPreferredTo W 𝒜 𝒞 ∧
      SourceTheory.Uniform.IsMoreInsensitive W 𝒜 𝒞 B D ∧ SourceTheory.Uniform.IsMoreInsensitive W 𝒞 𝒜 B D := by sorry

end SourceTheory.EqualSources
