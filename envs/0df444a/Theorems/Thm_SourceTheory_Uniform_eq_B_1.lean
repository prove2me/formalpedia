-- Prove2me | Theorems.Thm_SourceTheory_Uniform_eq_B_1
-- name    : SourceTheory.Uniform.eq_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:05.521994+00:00
-- url     : https://prove2.me/theorems/44be391c-152a-4b5f-8e61-b1776ade5b12
-- title:
--   Equation (B.1), p. 8780 — if 𝒮 is preferred to itself, A ≽ C ⟺ Aᶜ ≼ Cᶜ on 𝒮
-- statement:
--   Work under structural Assumption 1 and let $\mathcal S$ be a source that is preferred to itself (Definition 2 with $\mathcal A=\mathcal C=\mathcal S$). Then for all events $A, C\in\mathcal S$,
--   $$W(A)\ge W(C)\ \Longleftrightarrow\ W(A^c)\le W(C^c),$$
--   that is, $A\succcurlyeq C \iff A^c \preccurlyeq C^c$ (B.1).
--
--   Within a self-preferred source, ranking events and ranking their complements are thus dual; the proof of Theorem 1 uses this throughout.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 1, Equation (B.1), p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set

/-- Equation (B.1) (App. B, proof of Theorem 1, p. 8780): if `𝒮` is preferred to itself, then for
events `A, C` from `𝒮`, `A ≽ C ⟺ Aᶜ ≼ Cᶜ`. -/
theorem eq_B_1 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮) (hpref : IsPreferredTo W 𝒮 𝒮) :
    ∀ A ∈ 𝒮, ∀ C ∈ 𝒮, W C ≤ W A ↔ W (Aᶜ) ≤ W (Cᶜ) := by sorry

end SourceTheory.Uniform
