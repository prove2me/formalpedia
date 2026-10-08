-- Prove2me | Theorems.Thm_StochasticOrders_MonotoneConvex_icx_submartingale_coupling_iff_v2
-- name    : StochasticOrders.MonotoneConvex.icx_submartingale_coupling_iff_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:18.046767+00:00
-- url     : https://prove2.me/theorems/8e454fc3-100a-4926-89a2-cfa14bdbeace
-- title:
--   Theorem 4.A.5 (increasing convex case) — submartingale-coupling characterization of the increasing convex order (corrected: finite means, random variables)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be random variables with finite means (measurable and integrable, the standing assumption of Chapters 3–4). Then
--
--   $$X \le_{icx} Y \iff \exists\,(\Omega'',\rho),\ \hat X,\hat Y:\Omega''\to\mathbb{R} \text{ random variables with } \hat X =_{st} X,\ \hat Y =_{st} Y,\ \text{and } \{\hat X,\hat Y\} \text{ a submartingale},$$
--
--   i.e. $E[\hat Y \mid \hat X] \ge \hat X$ a.s. **Furthermore**, $\hat X$ and $\hat Y$ can be selected such that $[\hat Y \mid \hat X = x]$ is increasing in $x$ in the usual stochastic order $\le_{st}$. This is the increasing-convex analogue of Strassen's martingale coupling (Theorem 3.A.4); the book states that the proof is similar. The reverse direction is Jensen's inequality applied to increasing convex functions.
--
--   **Formalization Note.** The retired version assumed no integrability: for $Y = 1/\omega$ on $(0,1]$ (positive, infinite mean) only test functions constant on $[0,\infty)$ are integrable, so $1 \le_{icx} Y$ held, while Mathlib's conditional expectation of the non-integrable $\hat Y$ is the junk value $0$ and the submartingale clause read $\hat X \le 0$; the forward direction was refuted. The new statement makes the standing finite-mean assumption explicit (`Integrable X μ`, `Integrable Y ν`) and requires $X$, $Y$, $\hat X$, $\hat Y$ to be measurable (random variables); `Measurable X̂` is moreover what makes $\sigma(\hat X)$ a sub-σ-algebra of the ambient one, without which Mathlib's `ρ[Ŷ | σ(X̂)]` is again $0$ (`condExp_of_not_le`). The submartingale condition is `X̂ ≤ᵐ[ρ] ρ[Ŷ | MeasurableSpace.comap X̂ _]`. The book's "$[\hat Y \mid \hat X = x]$ is increasing in $x$ in $\le_{st}$" is a property of a *version* of the conditional distribution, which is defined only up to null sets; it is formalized as the existence of a Markov kernel $\kappa$ disintegrating the joint law, $\rho\circ(\hat X,\hat Y)^{-1} = (\rho\circ\hat X^{-1}) \otimes \kappa$ (`ρ.map (X̂, Ŷ) = ρ.map X̂ ⊗ₘ κ`), whose survival functions $t \mapsto \kappa(x,(t,\infty))$ are monotone in $x$ at every threshold $t$ — the usual stochastic order between the measures $\kappa(x_1,\cdot)$ and $\kappa(x_2,\cdot)$. The retired version demanded this of Mathlib's specific `condDistrib` at *every* real $x$, including points outside the support of $\hat X$ where that version is construction-dependent (a Lean artefact, not the book's claim). The increasing convex order is the imported `IcxOrder` (increasing convex test functions with both expectations existing), which for integrable $X$, $Y$ is equivalent to the book's definition. The increasing concave case of Theorem 4.A.5 is the separate `icv_supermartingale_coupling_iff_v2`. Conventions made explicit: random variables are measurable functions on probability spaces (the book's standing convention, stated as `Measurable` hypotheses and `IsProbabilityMeasure` instances); "$=_{st}$" is `ProbabilityTheory.IdentDistrib`; the common space $(\Omega'',\rho)$ is existentially quantified, and the coupled copies are themselves random variables. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 183, Theorem 4.A.5

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory ProbabilityTheory

/-- Theorem 4.A.5 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 183), increasing
convex case: for random variables `X`, `Y` with finite means, `X ≤icx Y` if, and only if, there
exist two random variables `X̂` and `Ŷ`, defined on the same probability space, such that
`X̂ =st X`, `Ŷ =st Y`, and `{X̂, Ŷ}` is a submartingale, that is, `E[Ŷ | X̂] ≥ X̂` a.s.
Furthermore, `X̂` and `Ŷ` can be selected such that `[Ŷ | X̂ = x]` is increasing in `x` in the
usual stochastic order `≤st`.

Corrected version (`_v2`) of `icx_submartingale_coupling_iff`: (1) the standing finite-mean
assumption of Chapters 3–4 is explicit (`Integrable X μ`, `Integrable Y ν`); without it
`ρ[Ŷ | ·]` of a non-integrable `Ŷ` is Mathlib's junk `0` and the forward direction failed.
(2) `X`, `Y`, `X̂`, `Ŷ` are random variables (`Measurable`); `Measurable X̂` is also what makes
the conditional expectation meaningful (`condExp_of_not_le`). (3) the "Furthermore" clause is
stated as the existence of a Markov kernel `κ` disintegrating the joint law
(`ρ.map (X̂, Ŷ) = ρ.map X̂ ⊗ₘ κ`) whose survival functions are monotone in the conditioning
value, rather than a condition at every real `x` on Mathlib's specific `condDistrib` version. -/
theorem icx_submartingale_coupling_iff_v2 {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXint : Integrable X μ) (hYint : Integrable Y ν) :
    IcxOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] ∧
        ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧
          ρ.map (fun ω => (Xhat ω, Yhat ω)) = (ρ.map Xhat) ⊗ₘ κ ∧
          ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ, κ x₁ {y : ℝ | t < y} ≤ κ x₂ {y : ℝ | t < y} := by sorry

end StochasticOrders.MonotoneConvex
