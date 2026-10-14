-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_theorem_1
-- name    : SourceTheory.EqualSources.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:04.262498+00:00
-- url     : https://prove2.me/theorems/cefb9b85-6436-429d-8cda-de5dfd3ec4fb
-- title:
--   Theorem 1, p. 8774 — a source is uniform iff it is equally preferred and insensitive to itself w.r.t. a regular insensitivity region
-- statement:
--   Let $\succcurlyeq$, $U$ and $W$ satisfy structural Assumption 1 on the events $\mathcal E$, and let $\mathcal S$ be a source. The following two statements are equivalent.
--   1. Source theory (Definition 1) holds for $\mathcal S$: there is a probability measure $P_{\mathcal S}$ on $\mathcal S$ such that, for all acts $x, y$ from $\mathcal S$,
--   $$\big[\forall \alpha \in \Gamma:\ P_{\mathcal S}(x \succcurlyeq \alpha) \ge P_{\mathcal S}(y \succcurlyeq \alpha)\big] \implies x \succcurlyeq y.$$
--   2. $\mathcal S$ is equally preferred and insensitive to itself with respect to a regular insensitivity region: $\mathcal S$ is preferred to itself (Definition 2), and there are events $B, D \in \mathcal E$ such that $[B, D]$ is regular for $\mathcal S$ and $\mathcal S$ is more insensitive than itself with region $[B, D]$ (Definition 4).
--
--   This is the paper's first main result, a behavioral foundation of probabilistic sophistication within one source. The proof of Theorem 4 applies it to each of the two sources compared there.
--
--   **Formalization Note.** For $\mathcal A = \mathcal C = \mathcal S$ the comparative relations in both directions coincide, so one copy of each suffices. The boundary events $B, D$ are events, not necessarily from $\mathcal S$. This statement is identical to the goal of mission 1 of this series; it is restated here because draft items cannot import one another.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Theorem 1, p. 8774

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- Theorem 1 (Baillon et al. 2025, p. 8774): under structural Assumption 1, for a source `𝒮` the
following are equivalent: (i) source theory (Definition 1) holds for `𝒮`, i.e. `𝒮` is uniform;
(ii) `𝒮` is equally preferred and insensitive to itself w.r.t. a regular insensitivity region
`[B, D]` (`B`, `D` events). -/
theorem theorem_1 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒮 : Set (Set S)) (h𝒮 : SourceTheory.Uniform.IsSource 𝓔 W 𝒮) :
    SourceTheory.Uniform.IsUniform pref U 𝒮 ↔
      (SourceTheory.Uniform.IsPreferredTo W 𝒮 𝒮 ∧
        ∃ B ∈ 𝓔, ∃ D ∈ 𝓔, SourceTheory.Uniform.IsRegularRegion W 𝒮 B D ∧ SourceTheory.Uniform.IsMoreInsensitive W 𝒮 𝒮 B D) := by sorry

end SourceTheory.EqualSources
