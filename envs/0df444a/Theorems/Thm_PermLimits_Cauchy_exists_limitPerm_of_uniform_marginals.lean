-- Prove2me | Theorems.Thm_PermLimits_Cauchy_exists_limitPerm_of_uniform_marginals
-- name    : PermLimits.Cauchy.exists_limitPerm_of_uniform_marginals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:24:30.178082+00:00
-- url     : https://prove2.me/theorems/694571bd-fe0d-4429-8e98-31bdfba319e1
-- title:
--   Lemma 2.2 (a): every law on $[0,1]^2$ with uniform marginals has a limit permutation
-- statement:
--   Let $(X,Y)$ be a $[0,1]^2$-valued random variable with $X\sim U[0,1]$ and $Y\sim U[0,1]$. Then there is a limit permutation $Z\in\mathcal Z$ such that
--   $$\mathbf P(X\in B,\;Y\le y)=\int_0^1 Z(x,y)\,\mathbf 1[x\in B]\,dx\qquad\text{for every Borel set } B\subseteq[0,1] \text{ and every } y\in[0,1]. \tag{19}$$
--
--   In words, $Z$ is a regular conditional distribution function of $Y$ given $X$. The lemma is how a limit permutation is obtained from a weak limit of random points with uniform marginals.
--
--   **Formalization Note** Only part (a) of the source's Lemma 2.2 is stated. The random variable $(X,Y)$ is represented by its law $\mu$, a probability measure on $[0,1]^2$; the uniform marginals say that the images of $\mu$ under the two coordinate projections are Lebesgue measure on $[0,1]$. Probabilities are real numbers.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 9, Lemma 2.2 (a) (Eq. (19)); proof in Appendix A

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
open PermLimits.Shared

namespace PermLimits.Cauchy

open MeasureTheory unitInterval

/-- **Lemma 2.2 (a)** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 9;
proof in Appendix A). Let `(X, Y)` be a `[0,1]²`-valued random variable with `X, Y ∼ U[0, 1]`.
Then there is a limit permutation `Z` such that for every Borel set `B ⊆ [0, 1]` and every
`y ∈ [0, 1]`, `P(X ∈ B, Y ≤ y) = ∫₀¹ Z(x, y) 1[x ∈ B] dx` (Eq. (19)).

**Formalization Note.** Only part (a) of Lemma 2.2 is stated. The random variable `(X, Y)` is
represented by its law `μ`, a probability measure on `[0,1]²`; `X, Y ∼ U[0, 1]` says that both
marginals `μ ∘ Prod.fst⁻¹`, `μ ∘ Prod.snd⁻¹` are Lebesgue measure on `[0, 1]`.
`∫₀¹ Z(x, y) 1[x ∈ B] dx` is the set integral over `B`, and probabilities are `Measure.real`. -/
theorem exists_limitPerm_of_uniform_marginals (μ : Measure (I × I)) [IsProbabilityMeasure μ]
    (hX : μ.map Prod.fst = volume) (hY : μ.map Prod.snd = volume) :
    ∃ Z : I → I → ℝ, IsLimitPerm Z ∧
      ∀ B : Set I, MeasurableSet B → ∀ y : I,
        μ.real (B ×ˢ Set.Iic y) = ∫ x in B, Z x y := by sorry

end PermLimits.Cauchy
