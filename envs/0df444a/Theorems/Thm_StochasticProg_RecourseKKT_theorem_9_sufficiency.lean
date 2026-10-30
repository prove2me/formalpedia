-- Prove2me | Theorems.Thm_StochasticProg_RecourseKKT_theorem_9_sufficiency
-- name    : StochasticProg.RecourseKKT.theorem_9_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:53:07.340061+00:00
-- url     : https://prove2.me/theorems/05c9c22c-4578-4bf8-ac2a-a2fc9e712e33
-- title:
--   Theorem 9, sufficiency — the KKT condition (1.12) implies optimality
-- statement:
--   Consider a two-stage stochastic linear program with fixed recourse on a probability space, and let $x^* \in K_1$. If there exist $\lambda^* \in \mathbb R^{m_1}$ and $\mu^* \in \mathbb R^{n_1}$ with $\mu^* \ge 0$ and $\mu^{*\mathsf T} x^* = 0$ such that
--
--   $$
--   -c + A^{\mathsf T} \lambda^* + \mu^* \in \partial \mathcal Q(x^*), \tag{1.12}
--   $$
--
--   then $x^*$ is optimal in (1.2): $c^{\mathsf T}x^* + \mathcal Q(x^*) \le c^{\mathsf T}x + \mathcal Q(x)$ for every $x \in K_1$.
--
--   This is the "if" direction of Theorem 9. It needs none of that theorem's hypotheses (finite optimal value, finite second moments, $Q \ne -\infty$).
--
--   Differences from the source:
--   - generalization: under a finite optimal value of (1.2), finite second moments of ξ and Q ≠ −∞ → no such hypothesis; reason: the sufficiency holds without them; adding them back gives the book's statement
--   - encoding: ∂f(x) = {η | f(w) ≥ f(x) + ηᵀ(w − x) ∀w} → subdifferential with f(x) required real (empty where f(x) = ±∞); reason: the convex-analysis convention for extended-valued functions; at points where 𝒬 is finite it is the book's set
--   - encoding: 𝒬(x) = E_ξ Q(x, ξ) with +∞ + (−∞) = +∞ and 0·∞ = 0 → EReal value: +∞ if ∫⁻ Q⁺ = ∞, else ∫⁻ Q⁺ − ∫⁻ Q⁻; reason: the book's convention written out; same instances
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, Theorem 9 ('if' direction), printed p. 116 (PDF p. 141)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
import Definitions.Def_StochasticProg_RecourseKKT_firstStageSet
import Definitions.Def_StochasticProg_RecourseKKT_IsOptimalDEP
import Definitions.Def_StochasticProg_RecourseKKT_subdifferential
open MeasureTheory Matrix

namespace StochasticProg.RecourseKKT

/-- **Theorem 9, sufficiency (the "if" direction).**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, Theorem 9, printed p. 116 (PDF p. 141): "A solution x* ∈ K₁, is optimal in
(1.2) if … there exists some λ* ∈ ℜ^{m1}, μ* ∈ ℜ^{n1}_+, μ*ᵀx* = 0, such that,
−c + Aᵀλ* + μ* ∈ ∂𝒬(x*). (1.12)"

If `x* ∈ K₁` and there are `λ* ∈ ℜ^{m1}`, `μ* ≥ 0` with `μ*ᵀx* = 0` and
`−c + Aᵀλ* + μ* ∈ ∂𝒬(x*)`, then `x*` minimizes `cᵀx + 𝒬(x)` over `K₁`.

**Formalization Note.** This direction needs none of the book's hypotheses (finite optimal value,
finite second moments, `Q ≠ −∞`); they are dropped, which makes the statement more general. -/
theorem theorem_9_sufficiency {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet pb.A pb.b)
    (hkkt : ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
          -pb.c + pb.Aᵀ *ᵥ lam + mu ∈ subdifferential (expectedRecourse P pb) xs) :
    IsOptimalDEP P pb xs := by sorry

end StochasticProg.RecourseKKT
