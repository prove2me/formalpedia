-- Prove2me | Theorems.Thm_PermLimits_Existence_regular_conditional_cdf
-- name    : PermLimits.Existence.regular_conditional_cdf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:59:02.149205+00:00
-- url     : https://prove2.me/theorems/dda36211-21a8-4eb4-b474-67641d9efa6f
-- title:
--   Lemma 2.2: every point law with uniform marginals has an a.e. unique limit permutation
-- statement:
--   Let $(X,Y)$ be a $[0,1]^2$-valued random variable with $X,Y\sim U[0,1]$.
--
--   1. There exists a limit permutation $Z$ such that for every Borel set $B\subseteq[0,1]$ and every $y\in[0,1]$,
--   $$\mathbf P(X\in B,\,Y\le y)=\int_0^1 Z(x,y)\,\mathbf 1[x\in B]\,dx. \tag{19}$$
--   2. If $Z$ and $\hat Z$ are limit permutations both satisfying (19), then
--   $$\int_0^1\mathbf 1\big[\exists y\in[0,1]: Z(x,y)\ne\hat Z(x,y)\big]\,dx=0. \tag{20}$$
--
--   $Z$ is the regular conditional distribution function of $Y$ given $X$. The lemma says limit permutations and laws on the unit square with uniform marginals are in one-to-one correspondence up to null sets of $x$.
--
--   **Formalization Note** The random variable is represented by its law $\mu$, a probability measure on $[0,1]^2$ whose two marginals are Lebesgue measure. The source states part 2 for the $Z$ of part 1 and another $\hat Z$; here it is stated for any two limit permutations satisfying (19), which is the same statement. (20) is stated as: the set of $x$ with $Z(x,\cdot)\ne\hat Z(x,\cdot)$ has Lebesgue (outer) measure $0$.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 9, Lemma 2.2 (Eqs. (19)–(20)); proof in Appendix A, pp. 19–21

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
open PermLimits.Shared

namespace PermLimits.Existence

open MeasureTheory unitInterval

/-- **Lemma 2.2** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 9;
proof in Appendix A). Let `(X, Y)` be a `[0,1]²`-valued random variable with `X, Y ∼ U[0, 1]`.
(a) There is a limit permutation `Z` such that for every Borel set `B ⊆ [0, 1]` and every
`y ∈ [0, 1]`, `P(X ∈ B, Y ≤ y) = ∫₀¹ Z(x, y) 1[x ∈ B] dx` (Eq. (19)).
(b) If `Z` and `Ẑ` are limit permutations both satisfying (19), then
`∫₀¹ 1[∃ y ∈ [0,1] : Z(x, y) ≠ Ẑ(x, y)] dx = 0` (Eq. (20)).

**Formalization Note.** The paper's `Ẑ` is written `Z'`. The random variable `(X, Y)` is represented by its law `μ`, a probability
measure on `[0,1]²`; `X, Y ∼ U[0, 1]` says that both marginals `μ ∘ Prod.fst⁻¹`,
`μ ∘ Prod.snd⁻¹` are Lebesgue measure on `[0, 1]`. `∫₀¹ Z(x, y) 1[x ∈ B] dx` is the set integral
over `B`. Part (b) is stated for any two limit permutations satisfying (19) (the paper: `Z` from
(a) and another `Ẑ`); (20) is stated as `volume {x | ∃ y, Z x y ≠ Ẑ x y} = 0`, which for a
measurable set is the vanishing of the integral of its indicator, and in general says the set is
Lebesgue-null. -/
theorem regular_conditional_cdf (μ : Measure (I × I)) [IsProbabilityMeasure μ]
    (hX : μ.map Prod.fst = volume) (hY : μ.map Prod.snd = volume) :
    (∃ Z : I → I → ℝ, IsLimitPerm Z ∧
      ∀ B : Set I, MeasurableSet B → ∀ y : I,
        μ.real (B ×ˢ Set.Iic y) = ∫ x in B, Z x y) ∧
    (∀ Z Z' : I → I → ℝ, IsLimitPerm Z → IsLimitPerm Z' →
      (∀ B : Set I, MeasurableSet B → ∀ y : I, μ.real (B ×ˢ Set.Iic y) = ∫ x in B, Z x y) →
      (∀ B : Set I, MeasurableSet B → ∀ y : I, μ.real (B ×ˢ Set.Iic y) = ∫ x in B, Z' x y) →
      volume {x : I | ∃ y : I, Z x y ≠ Z' x y} = 0) := by sorry

end PermLimits.Existence
