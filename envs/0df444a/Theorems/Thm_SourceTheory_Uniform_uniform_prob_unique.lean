-- Prove2me | Theorems.Thm_SourceTheory_Uniform_uniform_prob_unique
-- name    : SourceTheory.Uniform.uniform_prob_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:16.282681+00:00
-- url     : https://prove2.me/theorems/6456ddf9-b376-425f-ab6d-20b054fd0b80
-- title:
--   Remark after Theorem 1, p. 8774 — the probability measure of a uniform source is uniquely determined
-- statement:
--   Work under structural Assumption 1 and let $\mathcal S$ be a source. If $\mathcal S$ is uniform with probability measure $P$ and also uniform with probability measure $Q$ (both finitely additive probability measures on $\mathcal S$ satisfying stochastic dominance (2) for all acts from $\mathcal S$), then
--   $$P(E)=Q(E)\qquad\text{for all } E\in\mathcal S.$$
--
--   Hence the a-neutral probability measure $P_{\mathcal S}$ and the source function $w_{\mathcal S}$ of a uniform source are well defined.
-- source:
--   Baillon et al. (2025), Management Science 71(10), §7, remark after Theorem 1, p. 8774

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set

/-- Remark after Theorem 1 (p. 8774): the probability measure of a uniform source is uniquely
determined — any two probability measures on `𝒮` with which `𝒮` is uniform agree on `𝒮`. -/
theorem uniform_prob_unique {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (h1 : Assumption1 𝓔 pref U W) (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮)
    (P Q : Set S → ℝ) (hP : IsUniformWith pref U 𝒮 P) (hQ : IsUniformWith pref U 𝒮 Q) :
    ∀ E ∈ 𝒮, P E = Q E := by sorry

end SourceTheory.Uniform
