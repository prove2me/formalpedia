-- Prove2me | Theorems.Thm_SourceTheory_Uniform_lemma_B_1
-- name    : SourceTheory.Uniform.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:10.671119+00:00
-- url     : https://prove2.me/theorems/d0e2fe9e-feac-4aa4-bdc3-5f2883db9f20
-- title:
--   Lemma B.1, p. 8780 — for E ∩ H = F ∩ H = ∅: E ≽ F ⟺ E ∪ H ≽ F ∪ H
-- statement:
--   Work under structural Assumption 1 and let $\mathcal S$ be a source satisfying statement (ii) of Theorem 1: $\mathcal S$ is preferred to itself, and for events $B, D$ the region $[B,D]$ is regular for $\mathcal S$ and $\mathcal S$ is more insensitive than itself with region $[B,D]$. Then for all events $E, F, H\in\mathcal S$ with $E\cap H = F\cap H=\emptyset$,
--   $$W(E)\ge W(F)\ \Longleftrightarrow\ W(E\cup H)\ge W(F\cup H),$$
--   i.e. $E\succcurlyeq F \iff E\cup H \succcurlyeq F\cup H$.
--
--   This is de Finetti's additivity axiom for the qualitative probability $\succcurlyeq$ on $\mathcal S$, the key step towards a representing probability measure.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Lemma B.1, p. 8780 (context: App. B, proof of Theorem 1, pp. 8779–8780)

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set

/-- Lemma B.1 (p. 8780), in the context of the proof of Theorem 1 (statement (ii) holds): for events
`E, F, H` from `𝒮` with `E ∩ H = F ∩ H = ∅`, `E ≽ F ⟺ E ∪ H ≽ F ∪ H`. -/
theorem lemma_B_1 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮) (hpref : IsPreferredTo W 𝒮 𝒮)
    (B D : Set S) (hB : B ∈ 𝓔) (hD : D ∈ 𝓔) (hreg : IsRegularRegion W 𝒮 B D)
    (hins : IsMoreInsensitive W 𝒮 𝒮 B D) :
    ∀ E ∈ 𝒮, ∀ F ∈ 𝒮, ∀ H ∈ 𝒮, E ∩ H = ∅ → F ∩ H = ∅ →
      (W F ≤ W E ↔ W (F ∪ H) ≤ W (E ∪ H)) := by sorry

end SourceTheory.Uniform
