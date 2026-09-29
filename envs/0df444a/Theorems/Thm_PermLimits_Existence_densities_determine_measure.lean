-- Prove2me | Theorems.Thm_PermLimits_Existence_densities_determine_measure
-- name    : PermLimits.Existence.densities_determine_measure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:01:36.09456+00:00
-- url     : https://prove2.me/theorems/0f8c67fc-12fa-4ddf-ba49-964a32c4cd6d
-- title:
--   Lemma 5.1: pattern densities determine the law of the random point
-- statement:
--   Let $Z,\hat Z\in\mathcal Z$ with associated random points $(X,Y)$ and $(\hat X,\hat Y)$. Then
--   $$\forall\tau\in\mathcal S:\ t(\tau,Z)=t(\tau,\hat Z)\implies (X,Y)\sim(\hat X,\hat Y).$$
--
--   Here $\mathcal S$ is the set of all finite permutations and $\sim$ means equality in distribution. The lemma is the uniqueness half of the theory: a limit permutation is determined, up to the null sets of Lemma 2.2, by its pattern densities.
--
--   **Formalization Note** Equality in distribution is equality of the laws $\mu_Z=\mu_{\hat Z}$ on $[0,1]^2$.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 15, Lemma 5.1

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_LimitMeasure
open PermLimits.Shared

namespace PermLimits.Existence

open unitInterval

/-- **Lemma 5.1** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 15).
Let `Z, Ẑ ∈ 𝒵`, with associated random points `(X, Y)` and `(X̂, Ŷ)` (Definition 2.3). If
`t(τ, Z) = t(τ, Ẑ)` for every permutation `τ`, then `(X, Y) ∼ (X̂, Ŷ)`.

**Formalization Note.** The paper's `Ẑ` is written `Z'`. `(X, Y) ∼ (X̂, Ŷ)` (same distribution, Sect. 2.1, p. 6) is equality of
the laws `limitMeasure Z = limitMeasure Ẑ`. `τ` ranges over permutations of every length. -/
theorem densities_determine_measure (Z Z' : I → I → ℝ) (hZ : IsLimitPerm Z) (hZ' : IsLimitPerm Z')
    (h : ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)), limitDensity τ Z = limitDensity τ Z') :
    limitMeasure Z = limitMeasure Z' := by sorry

end PermLimits.Existence
