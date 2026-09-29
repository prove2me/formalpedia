-- Prove2me | Theorems.Thm_PermLimits_Existence_limit_unique_ae
-- name    : PermLimits.Existence.limit_unique_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:03:38.259901+00:00
-- url     : https://prove2.me/theorems/ca10e998-23b2-4009-84ef-5f9bfed79bd9
-- title:
--   Theorem 1.7 (corrected): the limit of a permutation sequence is unique up to a null set of $x$
-- statement:
--   Let $Z_1,Z_2\in\mathcal Z$ and let $(\sigma_n)$ be a convergent permutation sequence with $\sigma_n\to Z_1$. Then
--   $$\sigma_n\to Z_2\iff \lambda\big(\{x: Z_1(x,\cdot)\not\equiv Z_2(x,\cdot)\}\big)=0,$$
--   where $\lambda$ is Lebesgue measure and $Z_1(x,\cdot)\not\equiv Z_2(x,\cdot)$ means $Z_1(x,y)\ne Z_2(x,y)$ for some $y\in[0,1]$.
--
--   A convergent permutation sequence therefore has an essentially unique limit: two limits can differ only on a null set of rows.
--
--   **Formalization Note** This is a correction of the source's statement, which reads "$\sigma_n\to Z_1$ and $\sigma_n\to Z_2$ if and only if the set $\{x: Z_1(x,\cdot)\not\equiv Z_2(x,\cdot)\}$ has Lebesgue measure zero". Read literally, its "if" direction fails: for $Z_1=Z_2$ the set is empty, yet $\sigma_n$ need not converge to $Z_1$. The source's proof establishes "only if", and the remark after Theorem 1.6 supplies "if" when $\sigma_n\to Z_1$. The statement here assumes $\sigma_n\to Z_1$ and asserts both directions for $Z_2$.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 5, Theorem 1.7; proof p. 18; remark after Theorem 1.6, p. 4

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_ConvergesTo
open PermLimits.Shared

namespace PermLimits.Existence

open MeasureTheory unitInterval

/-- **Theorem 1.7, corrected** (Hoppen et al., *Limits of permutation sequences*,
arXiv:1103.5844v2, p. 5; proof p. 18 and the remark after Theorem 1.6, p. 4). Let
`Z₁, Z₂ ∈ 𝒵` and let `(σ_m)` be a convergent permutation sequence with `σ_m → Z₁`. Then
`σ_m → Z₂` if and only if the set `{x : Z₁(x, ·) ≢ Z₂(x, ·)}` has Lebesgue measure zero.

**Formalization Note (correction).** The paper states "`σ_m → Z₁` and `σ_m → Z₂` if and only if
the set `{x : Z₁(x, ·) ≢ Z₂(x, ·)}` has Lebesgue measure zero". Read literally, the "if"
direction is false: take any sequence converging to some `Z₀` and `Z₁ = Z₂` differing from `Z₀`
on a set of `x` of positive measure; the set is empty but `σ_m ↛ Z₁`. The paper's proof (p. 18)
proves only "only if", and the remark after Theorem 1.6 (p. 4) supplies the "if" direction given
`σ_m → Z₁`. The statement here assumes `σ_m → Z₁` and asserts both directions for `Z₂`.
`Z₁(x, ·) ≢ Z₂(x, ·)` means `Z₁(x, y) ≠ Z₂(x, y)` for some `y ∈ [0, 1]`, as in Eq. (20).
The sequence is named `s` (`σ` is reserved notation once `unitInterval` is opened). -/
theorem limit_unique_ae (Z₁ Z₂ : I → I → ℝ) (hZ₁ : IsLimitPerm Z₁) (hZ₂ : IsLimitPerm Z₂)
    (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n)) (hs : IsConvergent s) (h₁ : ConvergesTo s Z₁) :
    ConvergesTo s Z₂ ↔ volume {x : I | ∃ y : I, Z₁ x y ≠ Z₂ x y} = 0 := by sorry

end PermLimits.Existence
