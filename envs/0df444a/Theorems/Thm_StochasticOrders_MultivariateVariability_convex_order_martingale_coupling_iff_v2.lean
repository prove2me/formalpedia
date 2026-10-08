-- Prove2me | Theorems.Thm_StochasticOrders_MultivariateVariability_convex_order_martingale_coupling_iff_v2
-- name    : StochasticOrders.MultivariateVariability.convex_order_martingale_coupling_iff_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:30.130486+00:00
-- url     : https://prove2.me/theorems/840b66f4-8c62-44ef-a797-84896c5db709
-- title:
--   Theorem 7.A.1 — martingale-coupling characterization of the multivariate convex order (corrected: finite means, random vectors)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be $n$-dimensional random vectors with finite means (measurable and integrable, the standing assumption of §7.A as of §3.A). Then $X \le_{cx} Y$ if, and only if, there exist two random vectors $\hat X$ and $\hat Y$, defined on the same probability space, such that
--
--   $$\hat X =_{st} X, \qquad \hat Y =_{st} Y, \qquad \{\hat X,\hat Y\}\text{ is a martingale, i.e. }E[\hat Y \mid \hat X] = \hat X \text{ a.s.}$$
--
--   This is the $n$-dimensional generalization of Strassen's Theorem 3.A.4. Unlike the univariate theorem, the book states no further "Furthermore" strengthening here.
--
--   **Formalization Note.** The retired version assumed no integrability: Mathlib's conditional expectation of a non-integrable $\hat Y$ is the junk value $0$, so for $X = Y = (1/x)$ on $(0,1]$ the order held reflexively while the martingale clause forced $\hat X = 0$ a.s., and the forward direction was refuted. The new statement makes the standing finite-mean assumption explicit (`Integrable X μ`, `Integrable Y ν`, i.e. every coordinate integrable) and requires $X$, $Y$, $\hat X$, $\hat Y$ to be measurable (random vectors); `Measurable X̂` is moreover what makes $\sigma(\hat X)$ a sub-σ-algebra of the ambient one, without which Mathlib's `ρ[Ŷ | σ(X̂)]` is again $0$ (`condExp_of_not_le`). The martingale condition is the `Fin n → ℝ`-valued conditional expectation `ρ[Ŷ | MeasurableSpace.comap X̂ _] =ᵐ[ρ] X̂`. The multivariate convex order is the imported `ConvexOrder` (convex test functions on $\mathbb{R}^n$ with both expectations existing), equivalent for integrable $X$, $Y$ to the book's definition. Conventions made explicit: random variables are measurable functions on probability spaces (the book's standing convention, stated as `Measurable` hypotheses and `IsProbabilityMeasure` instances); "$=_{st}$" is `ProbabilityTheory.IdentDistrib`; the common space $(\Omega'',\rho)$ is existentially quantified, and the coupled copies are themselves random variables. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 324, Theorem 7.A.1

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_ConvexOrder

namespace StochasticOrders.MultivariateVariability

open MeasureTheory ProbabilityTheory

/-- Theorem 7.A.1 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 324): random
vectors `X` and `Y` with finite means satisfy `X ≤cx Y` if, and only if, there exist two random
vectors `X̂` and `Ŷ`, defined on the same probability space, such that `X̂ =st X`, `Ŷ =st Y`, and
`{X̂, Ŷ}` is a martingale, that is, `E[Ŷ | X̂] = X̂` a.s. Unlike the univariate Theorem 3.A.4
and this chapter's own Theorem 7.A.2, the book states no further "Furthermore" strengthening.

Corrected version (`_v2`) of `convex_order_martingale_coupling_iff`: the standing finite-mean
assumption of §7.A (as of §3.A) is explicit (`Integrable X μ`, `Integrable Y ν`); without it
`ρ[Ŷ | ·]` of a non-integrable `Ŷ` is Mathlib's junk `0` and the forward direction failed. `X`,
`Y`, `X̂`, `Ŷ` are random vectors (`Measurable`); `Measurable X̂` is also what makes
`comap X̂ ≤ m` and hence the conditional expectation meaningful (`condExp_of_not_le`). -/
theorem convex_order_martingale_coupling_iff_v2 {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hXint : Integrable X μ) (hYint : Integrable Y ν) :
    ConvexOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → Fin n → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] =ᵐ[ρ] Xhat := by sorry

end StochasticOrders.MultivariateVariability
