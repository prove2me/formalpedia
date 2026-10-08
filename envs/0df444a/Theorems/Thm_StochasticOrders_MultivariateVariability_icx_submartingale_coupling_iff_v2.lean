-- Prove2me | Theorems.Thm_StochasticOrders_MultivariateVariability_icx_submartingale_coupling_iff_v2
-- name    : StochasticOrders.MultivariateVariability.icx_submartingale_coupling_iff_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:37.671091+00:00
-- url     : https://prove2.me/theorems/c484eb9d-53ef-48ae-9a6f-da6be0adaebf
-- title:
--   Theorem 7.A.2 (increasing convex case) — submartingale-coupling characterization of the multivariate increasing convex order (corrected: finite means, random vectors)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be $n$-dimensional random vectors with finite means (measurable and integrable, the standing assumption of §7.A). Then $X \le_{icx} Y$ if, and only if, there exist two random vectors $\hat X$ and $\hat Y$, defined on the same probability space, such that $\hat X =_{st} X$, $\hat Y =_{st} Y$, and $\{\hat X,\hat Y\}$ is a submartingale, that is,
--
--   $$E[\hat Y \mid \hat X] \ge \hat X \text{ a.s. (coordinatewise).}$$
--
--   This is the $n$-dimensional generalization of Theorem 4.A.5's increasing convex case, proved by the same method as Theorem 7.A.1. The book's bracketed increasing-concave companion is a separate statement and is not drafted here; the book states no "Furthermore" clause for this theorem.
--
--   **Formalization Note.** The retired version assumed no integrability: Mathlib's conditional expectation of a non-integrable $\hat Y$ is the junk value $0$, so for $X = Y = (1/x)$ on $(0,1]$ the order held reflexively while the submartingale clause forced $\hat X \le 0$ a.s., and the forward direction was refuted. The new statement makes the standing finite-mean assumption explicit (`Integrable X μ`, `Integrable Y ν`) and requires $X$, $Y$, $\hat X$, $\hat Y$ to be measurable (random vectors); `Measurable X̂` is moreover what makes $\sigma(\hat X)$ a sub-σ-algebra of the ambient one, without which Mathlib's `ρ[Ŷ | σ(X̂)]` is again $0$ (`condExp_of_not_le`). The submartingale condition is `X̂ ≤ᵐ[ρ] ρ[Ŷ | MeasurableSpace.comap X̂ _]` with the coordinatewise order on `Fin n → ℝ`. The multivariate increasing convex order is the imported `IcxOrder`, equivalent for integrable $X$, $Y$ to the book's definition. Conventions made explicit: random variables are measurable functions on probability spaces (the book's standing convention, stated as `Measurable` hypotheses and `IsProbabilityMeasure` instances); "$=_{st}$" is `ProbabilityTheory.IdentDistrib`; the common space $(\Omega'',\rho)$ is existentially quantified, and the coupled copies are themselves random variables. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 324, Theorem 7.A.2

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_IcxOrder

namespace StochasticOrders.MultivariateVariability

open MeasureTheory ProbabilityTheory

/-- Theorem 7.A.2 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 324), increasing
convex case: two random vectors `X` and `Y` with finite means satisfy `X ≤icx Y` if, and only if,
there exist two random vectors `X̂` and `Ŷ`, defined on the same probability space, such that
`X̂ =st X`, `Ŷ =st Y`, and `{X̂, Ŷ}` is a submartingale, that is, `E[Ŷ | X̂] ≥ X̂` a.s. (The
book's bracketed increasing-concave companion is a separate statement, not drafted here.)

Corrected version (`_v2`) of `icx_submartingale_coupling_iff`: the standing finite-mean
assumption of §7.A is explicit (`Integrable X μ`, `Integrable Y ν`); without it `ρ[Ŷ | ·]` of a
non-integrable `Ŷ` is Mathlib's junk `0` and the forward direction failed. `X`, `Y`, `X̂`, `Ŷ`
are random vectors (`Measurable`); `Measurable X̂` is also what makes `comap X̂ ≤ m` and hence
the conditional expectation meaningful (`condExp_of_not_le`). -/
theorem icx_submartingale_coupling_iff_v2 {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hXint : Integrable X μ) (hYint : Integrable Y ν) :
    IcxOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → Fin n → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] := by sorry

end StochasticOrders.MultivariateVariability
