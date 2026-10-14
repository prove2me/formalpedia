-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_regularity_bound
-- name    : SourceTheory.EqualSources.regularity_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:07.79851+00:00
-- url     : https://prove2.me/theorems/fb8b4df3-734b-4449-a335-e1fed329c947
-- title:
--   §7, p. 8774 — for a uniform source and B, D from it, a regular region has P(B) ≤ 1/4 ≤ 3/4 ≤ P(D)
-- statement:
--   Let $\mathcal S$ be a source (a subalgebra of the events on which $W$ is convex ranged) that is uniform with a-neutral probability measure $P$, and let $w$ be its source function, so $W = w \circ P$ on $\mathcal S$ with $w$ a continuous probability weighting function. Let $B, D \in \mathcal S$ be such that the insensitivity region $[B, D]$ is regular for $\mathcal S$. Then
--
--   $$P(B) \le \tfrac14 \le \tfrac34 \le P(D).$$
--
--   Regularity thus forces an insensitivity region to cover at least the middle half of the probability scale. The proof of Theorem 4 uses this to conclude that the upper bound of the region exceeds $1/2$.
--
--   **Formalization Note.** "Take $\mathcal S$ uniform" is encoded as uniformity with $P$ together with the source function $w$ of (5), p. 8771, which the paper attaches to every uniform source. Structural Assumption 1 is not needed and is not assumed, which makes the statement stronger.
-- source:
--   Baillon et al. (2025), Management Science 71(10), §7, definition of regularity, p. 8774

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- The regularity bound (§7, p. 8774): for a uniform source `𝒮` with a-neutral probability `P` and
source function `w`, a regular insensitivity region `[B, D]` with `B, D` from `𝒮` has
`P(B) ≤ 1/4 ≤ 3/4 ≤ P(D)`. -/
theorem regularity_bound {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ)
    (𝒮 : Set (Set S)) (h𝒮 : SourceTheory.Uniform.IsSource 𝓔 W 𝒮) (P : Set S → ℝ) (w : ℝ → ℝ)
    (hP : SourceTheory.Uniform.IsUniformWith pref U 𝒮 P) (hw : SourceTheory.Uniform.IsSourceFunction W 𝒮 P w)
    (B D : Set S) (hB : B ∈ 𝒮) (hD : D ∈ 𝒮) (hreg : SourceTheory.Uniform.IsRegularRegion W 𝒮 B D) :
    P B ≤ 1 / 4 ∧ (3 / 4 : ℝ) ≤ P D := by sorry

end SourceTheory.EqualSources
