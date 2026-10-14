-- Prove2me | Theorems.Thm_SourceTheory_Uniform_source_function_of_representing
-- name    : SourceTheory.Uniform.source_function_of_representing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:23.286558+00:00
-- url     : https://prove2.me/theorems/49f221d7-f4c2-4fa4-a3ee-ef9cb3dd2c11
-- title:
--   Proof of Theorem 1 (aside), p. 8780 — a representing P yields W = w ∘ P on 𝒮 with w continuous and strictly increasing
-- statement:
--   Work under structural Assumption 1, let $\mathcal S$ be a source, and let $P$ be a probability measure on $\mathcal S$ that represents event preference on $\mathcal S$: $W(A)\ge W(A') \iff P(A)\ge P(A')$ for $A, A'\in\mathcal S$. Then there is a function $w:[0,1]\to[0,1]$, continuous and strictly increasing on $[0,1]$ with $w(0)=0$ and $w(1)=1$, such that
--   $$W(E) = w\bigl(P(E)\bigr)\qquad\text{for all } E\in\mathcal S.$$
--
--   So $w$ is a source function of $\mathcal S$ in the sense of (5): $W$ restricted to the source is a probability weighting of $P$.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 1, last paragraph (the aside), p. 8780; Observation 1, p. 8770

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set

/-- Proof of Theorem 1, the aside (App. B, p. 8780): if a probability measure `P` on the source
`𝒮` represents the preference relation on events from `𝒮`, then `W = w ∘ P` on `𝒮` for a
continuous, strictly increasing probability weighting function `w`. -/
theorem source_function_of_representing {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (h1 : Assumption1 𝓔 pref U W) (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮)
    (P : Set S → ℝ) (hP : IsProbOn 𝒮 P) (hrep : ∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A) :
    ∃ w : ℝ → ℝ, IsSourceFunction W 𝒮 P w := by sorry

end SourceTheory.Uniform
