-- Prove2me | Theorems.Thm_StochasticProg_RecourseKKT_theorem_6a
-- name    : StochasticProg.RecourseKKT.theorem_6a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:50:58.901772+00:00
-- url     : https://prove2.me/theorems/a551ec08-4d8d-408f-8f96-9ad4013ab55c
-- title:
--   Theorem 6(a) — the expected recourse function is Lipschitzian, convex and finite on $K_2$
-- statement:
--   Consider a two-stage stochastic linear program with fixed recourse on a probability space $(\Omega, \mathcal F, P)$. Assume that
--
--   1. $\xi = (q, h, T)$ has finite second moments, and
--   2. $Q(x,\xi) \ne -\infty$ for every $x$, almost surely.
--
--   Let $K_2 = \{x \mid \mathcal Q(x) < \infty\}$. Then $\mathcal Q$ is finite on $K_2$, $K_2$ is convex, $\mathcal Q$ is convex on $K_2$, and $\mathcal Q$ is Lipschitzian relative to $K_2$: there is a constant $L$ with
--
--   $$
--   |\mathcal Q(x) - \mathcal Q(w)| \le L\, \|x - w\| \qquad \text{for all } x, w \in K_2 .
--   $$
--
--   The book proves the Lipschitz clause by citation (Wets 1972, Kall 1976). It is the input of Theorem 9 ("supposing that $\xi$ has finite second moments, we know that $\mathcal Q$ is Lipschitzian", p. 115).
--
--   **Formalization Note** $\mathbb R^{n_1}$ carries the sup norm; another norm changes only $L$, which is existential. Since $\mathcal Q = +\infty$ off $K_2$, "convex function" is convexity of $K_2$ together with convexity of $\mathcal Q$ on it.
--
--   Differences from the source:
--   - generalization: Q(x, ξ) is not −∞ (for every x and ξ, p. 112) → for every x, Q(x, ξ(ω)) ≠ −∞ for P-almost every ω; reason: a weaker hypothesis, implied by the book's; null events do not affect 𝒬 (p. 110)
--   - encoding: ξ has finite second moments → every coordinate of q, h, T is in L²(P); reason: equivalent to E‖ξ‖² < ∞
--   - encoding: 𝒬(x) = E_ξ Q(x, ξ) with +∞ + (−∞) = +∞ and 0·∞ = 0 → EReal value: +∞ if ∫⁻ Q⁺ = ∞, else ∫⁻ Q⁺ − ∫⁻ Q⁻; reason: the book's convention written out; same instances
--   - encoding: 𝒬 is a Lipschitzian convex function, finite on K₂ → 𝒬 ≠ −∞ on K₂ (and < +∞ by definition of K₂), ConvexOn K₂ of its real value, LipschitzOnWith L on K₂ for some L; reason: 𝒬 = +∞ off K₂; 'Lipschitzian relative to X' is §2.11's notion; ℜ^{n1} with the sup norm, L existential
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1c, Theorem 6(a), printed p. 112 (PDF p. 137), with the standing assumption of the same page

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
import Definitions.Def_StochasticProg_RecourseKKT_secondStageFeasSet
import Definitions.Def_StochasticProg_RecourseKKT_FiniteSecondMoments
import Definitions.Def_StochasticProg_RecourseKKT_RecourseNotNegInf
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **Theorem 6(a) (the expected recourse function is Lipschitzian, convex, finite on `K₂`).**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1c, Theorem 6, printed p. 112 (PDF p. 137), under the standing assumption of
the same page ("We now turn to the properties of Q(x, ξ), assuming it is not −∞"):
"For a stochastic program with fixed recourse where ξ has finite second moments,
(a) 𝒬(x) is a Lipschitzian convex function and is finite on K₂."

If `ξ` has finite second moments and `Q(x, ξ) ≠ −∞` (almost surely, for every `x`), then on
`K₂ = {x | 𝒬(x) < ∞}`: `𝒬` is finite, `𝒬` is convex on the convex set `K₂`, and `𝒬` is
Lipschitz relative to `K₂` (§2.11, p. 99) for some constant `L`.

**Formalization Note.** `𝒬 = +∞` off `K₂` by definition, so "convex function" (in the extended
sense) is "convex domain and convex on it"; `ConvexOn ℝ K₂ f` includes the convexity of `K₂`. `ℜ^{n1}` is `Fin n1 → ℝ` with the sup norm; any other
norm changes only the constant `L`, which is existential. Theorem 6(b) is not part of this item. -/
theorem theorem_6a {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (hmom : FiniteSecondMoments P pb) (hnn : RecourseNotNegInf P pb) :
    (∀ x ∈ secondStageFeasSet P pb, expectedRecourse P pb x ≠ ⊥) ∧
      ConvexOn ℝ (secondStageFeasSet P pb) (fun x => (expectedRecourse P pb x).toReal) ∧
      ∃ L : NNReal,
        LipschitzOnWith L (fun x => (expectedRecourse P pb x).toReal)
          (secondStageFeasSet P pb) := by sorry

end StochasticProg.RecourseKKT
