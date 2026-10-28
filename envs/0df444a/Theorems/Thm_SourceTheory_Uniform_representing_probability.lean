-- Prove2me | Theorems.Thm_SourceTheory_Uniform_representing_probability
-- name    : SourceTheory.Uniform.representing_probability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:59.537804+00:00
-- url     : https://prove2.me/theorems/972bc187-3b10-4516-93ed-cababf67ed64
-- title:
--   Proof of Theorem 1, p. 8780 — under (ii), a unique probability measure on 𝒮 represents event preference
-- statement:
--   Work under structural Assumption 1 and let $\mathcal S$ be a source satisfying statement (ii) of Theorem 1: $\mathcal S$ is preferred to itself, and for events $B, D$ the region $[B,D]$ is regular for $\mathcal S$ and $\mathcal S$ is more insensitive than itself with region $[B,D]$. Then there is a probability measure $P$ on $\mathcal S$ (finitely additive, nonnegative, $P(S)=1$) that represents event preference on $\mathcal S$,
--   $$W(A)\ge W(A')\ \Longleftrightarrow\ P(A)\ge P(A')\qquad (A,A'\in\mathcal S),$$
--   and it is unique: every probability measure $Q$ on $\mathcal S$ with the same representation property agrees with $P$ on $\mathcal S$.
--
--   The paper obtains this from Lemma B.1, weak ordering, event solvability and Krantz et al. (1971, Theorem 5.2.2); with cumulative dominance it closes the sufficiency half of Theorem 1.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 1, last paragraph, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set

/-- Proof of Theorem 1 (App. B, p. 8780): if statement (ii) holds, there exists a unique
(finitely additive) probability measure `P` on the source `𝒮` that represents the preference
relation on events from `𝒮` (`A ≽ B ⟺ P(A) ≥ P(B)`). -/
theorem representing_probability {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (h1 : Assumption1 𝓔 pref U W) (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮)
    (hpref : IsPreferredTo W 𝒮 𝒮)
    (B D : Set S) (hB : B ∈ 𝓔) (hD : D ∈ 𝓔) (hreg : IsRegularRegion W 𝒮 B D)
    (hins : IsMoreInsensitive W 𝒮 𝒮 B D) :
    ∃ P : Set S → ℝ, IsProbOn 𝒮 P ∧ (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A) ∧
      ∀ Q : Set S → ℝ, IsProbOn 𝒮 Q → (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ Q A' ≤ Q A) →
        ∀ E ∈ 𝒮, Q E = P E := by sorry

end SourceTheory.Uniform
