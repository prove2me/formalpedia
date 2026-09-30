-- Prove2me | Theorems.Thm_PermLimits_Cauchy_supDist_le_rectDist_le
-- name    : PermLimits.Cauchy.supDist_le_rectDist_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:23:34.251469+00:00
-- url     : https://prove2.me/theorems/734e010a-5275-4b06-a6be-10f98d924cc6
-- title:
--   Eq. (34): $d_\infty\le d_\square\le 4\,d_\infty$
-- statement:
--   Let $Z_1,Z_2\in\mathcal Z$, let $d_\square$ be their rectangular distance and $d_\infty$ the sup-norm distance of their joint distribution functions. Then
--   $$d_\infty(Z_1,Z_2)\le d_\square(Z_1,Z_2)\le 4\cdot d_\infty(Z_1,Z_2). \tag{34}$$
--
--   The two distances are therefore equivalent on $\mathcal Z$: a sequence is Cauchy, or convergent, for one exactly when it is for the other. This is how completeness of the sup-norm on functions of the square is brought to bear on rectangular distance.
--
--   **Formalization Note** $d_\square$ is the integral form of the source's Eq. (32) and $d_\infty$ is Eq. (33) with the joint distribution function written as $\int_0^x Z_i(t,y)\,dt$. The constant $4$ is the source's.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 12, Sect. 4.1, Eq. (34)

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_RectDist
import Definitions.Def_PermLimits_Cauchy_SupDist
open PermLimits.Shared

namespace PermLimits.Cauchy

open unitInterval

/-- **Eq. (34)** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2,
Sect. 4.1, p. 12). For limit permutations `Z₁, Z₂ ∈ 𝒵`,
`d∞(Z₁, Z₂) ≤ d□(Z₁, Z₂) ≤ 4 · d∞(Z₁, Z₂)`.

**Formalization Note.** `d□` is the first line of Eq. (32) (`rectDist`) and `d∞` is Eq. (33) with
`Fᵢ(x, y) = ∫₀ˣ Zᵢ(t, y) dt` (`supDist`, see its note). The constant `4` is the paper's. -/
theorem supDist_le_rectDist_le (Z₁ Z₂ : I → I → ℝ) (hZ₁ : IsLimitPerm Z₁) (hZ₂ : IsLimitPerm Z₂) :
    supDist Z₁ Z₂ ≤ rectDist Z₁ Z₂ ∧ rectDist Z₁ Z₂ ≤ 4 * supDist Z₁ Z₂ := by sorry

end PermLimits.Cauchy
