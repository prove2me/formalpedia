-- Prove2me | Theorems.Thm_SourceTheory_Uniform_theorem_1_necessity
-- name    : SourceTheory.Uniform.theorem_1_necessity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:56.747264+00:00
-- url     : https://prove2.me/theorems/30298632-267f-4a8c-8d5a-1225c0b98da5
-- title:
--   Proof of Theorem 1, p. 8779 — a uniform source is preferred to and more insensitive than itself with the maximal region [∅, S]
-- statement:
--   Work under structural Assumption 1 with events $\mathcal E$, preference $\succcurlyeq$, utility $U$ and weighting function $W$, and let $\mathcal S$ be a source (a subalgebra of events on which $W$ is convex ranged). Suppose $\mathcal S$ is uniform: some probability measure $P$ on $\mathcal S$ satisfies stochastic dominance (2) for all acts from $\mathcal S$. Then
--
--   1. $\mathcal S$ is preferred to itself (Definition 2): for all $A_1, C_1 \in \mathcal S$,
--   $$W(A_1)=W(C_1)\ \Longrightarrow\ W(A_1^c)\le W(C_1^c);$$
--   2. $\mathcal S$ is more insensitive than itself (Definition 4) with the maximal insensitivity region $[\emptyset, S]$, i.e. (8) and (9) hold for all threefold partitions from $\mathcal S$ with $B=\emptyset$, $D=S$.
--
--   This is the necessity half of Theorem 1, together with the observation that the boundary conditions are not needed: the region can be taken maximal.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 1, first paragraph, p. 8779

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.Uniform

open Set

/-- Proof of Theorem 1, necessity (App. B, p. 8779): if `𝒮` is uniform, then `𝒮` is preferred to
itself and more insensitive than itself with the maximal insensitivity region `[∅, S]`. -/
theorem theorem_1_necessity {S Γ : Type*} (𝓔 : Set (Set S))
    (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (h1 : Assumption1 𝓔 pref U W) (𝒮 : Set (Set S)) (h𝒮 : IsSource 𝓔 W 𝒮)
    (hu : IsUniform pref U 𝒮) :
    IsPreferredTo W 𝒮 𝒮 ∧ IsMoreInsensitive W 𝒮 𝒮 ∅ univ := by sorry

end SourceTheory.Uniform
