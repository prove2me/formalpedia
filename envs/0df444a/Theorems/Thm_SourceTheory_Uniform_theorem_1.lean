-- Prove2me | Theorems.Thm_SourceTheory_Uniform_theorem_1
-- name    : SourceTheory.Uniform.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:34.25479+00:00
-- url     : https://prove2.me/theorems/376f6afd-1c1c-49c6-bf0e-f97a0aeade9f
-- title:
--   Theorem 1, p. 8774 — a source is uniform iff it is equally preferred and insensitive to itself w.r.t. a regular insensitivity region
-- statement:
--   Work under structural Assumption 1: events form an algebra $\mathcal E$ on a state space $S$, acts are finite-valued maps into an outcome set $\Gamma$, the preference $\succcurlyeq$ on acts is a weak order with biseparable utility given by a utility $U$ and a weighting function $W$, and convex rangedness, strong monotonicity, cumulative dominance, the Archimedean axiom and the existence of three nonindifferent outcomes hold. Let $\mathcal S$ be a source, i.e. a subalgebra of $\mathcal E$ on which $W$ is convex ranged. The following are equivalent:
--
--   1. source theory (Definition 1) holds for $\mathcal S$: there is a probability measure $P_{\mathcal S}$ on $\mathcal S$ with
--   $$\bigl[\forall\alpha\in\Gamma:\ P_{\mathcal S}(x\succcurlyeq\alpha)\ge P_{\mathcal S}(y\succcurlyeq\alpha)\bigr]\Longrightarrow x\succcurlyeq y\quad\text{for all acts } x,y \text{ from } \mathcal S;$$
--   2. $\mathcal S$ is equally preferred and insensitive to itself w.r.t. a regular insensitivity region: $\mathcal S$ is preferred to itself (Definition 2), and there are events $B, D\in\mathcal E$ such that $[B,D]$ is regular for $\mathcal S$ and $\mathcal S$ is more insensitive than itself with region $[B,D]$ (Definition 4).
--
--   This is a behavioral foundation of probabilistic sophistication within one source: uniformity is captured exactly by the two ambiguity attitudes, source preference and insensitivity, holding with equality between the source and itself.
--
--   **Formalization Note** Biseparable utility "holding for $\mathcal S$" in Definition 1 is part of Assumption 1 and is not repeated. For $\mathcal A = \mathcal C = \mathcal S$ the two directions of "equally preferred" and of "equally insensitive" are the same condition, so each is stated once. The boundary events $B, D$ are arbitrary events, not necessarily from $\mathcal S$; the region in statement 2 must be regular, which rules out the near-vacuous regions such as $B = S$, $D=\emptyset$. Events are ranked by $W$; the probability measure is finitely additive.
-- source:
--   Baillon et al. (2025), Management Science 71(10), Theorem 1, p. 8774; proof in App. B, pp. 8779–8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set

/-- Theorem 1 (Baillon et al. 2025, p. 8774): under structural Assumption 1, for a source `𝒮` the
following are equivalent: (i) source theory (Definition 1) holds for `𝒮`, i.e. `𝒮` is uniform;
(ii) `𝒮` is equally preferred and insensitive to itself w.r.t. a regular insensitivity region
`[B, D]` (`B`, `D` events). -/
theorem theorem_1 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮) :
    IsUniform pref U 𝒮 ↔
      (IsPreferredTo W 𝒮 𝒮 ∧
        ∃ B ∈ 𝓔, ∃ D ∈ 𝓔, IsRegularRegion W 𝒮 B D ∧ IsMoreInsensitive W 𝒮 𝒮 B D) := by sorry

end SourceTheory.Uniform
