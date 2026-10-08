-- Prove2me | Theorems.Thm_StochasticOrders_Convex_convex_order_martingale_coupling_iff_v2
-- name    : StochasticOrders.Convex.convex_order_martingale_coupling_iff_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:09.536551+00:00
-- url     : https://prove2.me/theorems/60df9050-7401-40af-bca8-d2d9d792d5e2
-- title:
--   Theorem 3.A.4 — Strassen's martingale-coupling characterization of the convex order (corrected: finite means, random variables)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be random variables with finite means (measurable and integrable, the standing assumption of §3.A). Then
--
--   $$X \le_{cx} Y \iff \exists\,(\Omega'',\rho),\ \hat X,\hat Y:\Omega''\to\mathbb{R} \text{ random variables with } \hat X =_{st} X,\ \hat Y =_{st} Y,\ \text{and } \{\hat X,\hat Y\} \text{ a martingale},$$
--
--   i.e. $E[\hat Y \mid \hat X] = \hat X$ a.s. **Furthermore**, $\hat X$ and $\hat Y$ can be selected such that $[\hat Y \mid \hat X = x]$ is increasing in $x$ in the usual stochastic order $\le_{st}$. This is Strassen's martingale-coupling characterization of the convex order (the mean-preserving spread of Rothschild–Stiglitz): $X \le_{cx} Y$ holds exactly when a copy of each can be built on a common probability space so that the copy of $Y$ is, conditionally on the copy of $X$, a fair randomization of it whose conditional law grows in $\le_{st}$ with the conditioning value. The reverse direction is Jensen's inequality; the book calls the constructive direction "not easy to prove".
--
--   **Formalization Note.** The retired version assumed no integrability: Mathlib's conditional expectation of a non-integrable $\hat Y$ is the junk value $0$, so for $X = Y = 1/x$ on $(0,1]$ the order held reflexively while the martingale clause forced $\hat X = 0$ a.s., and the forward direction was refuted. The new statement makes the standing finite-mean assumption explicit (`Integrable X μ`, `Integrable Y ν`), so $\hat Y$ is integrable and $E[\hat Y\mid\hat X]$ is the honest conditional expectation; it also requires $X$, $Y$, $\hat X$, $\hat Y$ to be measurable (random variables) — `Measurable X̂` is moreover what makes $\sigma(\hat X)$ a sub-σ-algebra of the ambient one, without which Mathlib's `ρ[Ŷ | σ(X̂)]` is again $0$ (`condExp_of_not_le`). The martingale condition is Mathlib's `ρ[Ŷ | MeasurableSpace.comap X̂ _] =ᵐ[ρ] X̂`. The book's "$[\hat Y \mid \hat X = x]$ is increasing in $x$ in $\le_{st}$" is a property of a *version* of the conditional distribution, which is defined only up to null sets; it is formalized as the existence of a Markov kernel $\kappa$ disintegrating the joint law, $\rho\circ(\hat X,\hat Y)^{-1} = (\rho\circ\hat X^{-1}) \otimes \kappa$ (`ρ.map (X̂, Ŷ) = ρ.map X̂ ⊗ₘ κ`), whose survival functions $t \mapsto \kappa(x,(t,\infty))$ are monotone in $x$ at every threshold $t$ — the usual stochastic order between the measures $\kappa(x_1,\cdot)$ and $\kappa(x_2,\cdot)$. The retired version demanded this of Mathlib's specific `condDistrib` at *every* real $x$, including points outside the support of $\hat X$ where that version is construction-dependent (a Lean artefact, not the book's claim). The convex order is the imported `ConvexOrder` (test functions convex $\varphi:\mathbb{R}\to\mathbb{R}$ with both $\varphi(X)$, $\varphi(Y)$ integrable), which for integrable $X$, $Y$ is equivalent to the book's "whenever the expectations exist". Conventions made explicit: random variables are measurable functions on probability spaces (the book's standing convention, stated as `Measurable` hypotheses and `IsProbabilityMeasure` instances); "$=_{st}$" is `ProbabilityTheory.IdentDistrib`; the common space $(\Omega'',\rho)$ is existentially quantified, and the coupled copies are themselves random variables. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 112, Theorem 3.A.4

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

namespace StochasticOrders.Convex

open MeasureTheory ProbabilityTheory

/-- Theorem 3.A.4 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 112): for random
variables `X`, `Y` with finite means, `X ≤cx Y` if, and only if, there exist two random variables
`X̂` and `Ŷ`, defined on the same probability space, such that `X̂ =st X`, `Ŷ =st Y`, and
`{X̂, Ŷ}` is a martingale, that is, `E[Ŷ | X̂] = X̂` a.s. Furthermore (folded into the same
witness, as the book states it as a strengthening of the same construction), `X̂` and `Ŷ` can be
selected such that `[Ŷ | X̂ = x]` is increasing in `x` in the usual stochastic order `≤st`.

Corrected version (`_v2`) of `convex_order_martingale_coupling_iff`: (1) the standing finite-mean
assumption of §3.A is explicit (`Integrable X μ`, `Integrable Y ν`); without it `ρ[Ŷ | ·]` of a
non-integrable `Ŷ` is Mathlib's junk `0` and the forward direction failed. (2) `X`, `Y`, `X̂`, `Ŷ`
are random variables (`Measurable`); `Measurable X̂` is also what makes `comap X̂ ≤ m` and hence
the conditional expectation meaningful (`condExp_of_not_le`). (3) "`[Ŷ | X̂ = x]` increasing in
`x`" is a property of a *version* of the conditional distribution: it is stated as the existence
of a Markov kernel `κ` disintegrating the joint law (`ρ.map (X̂, Ŷ) = ρ.map X̂ ⊗ₘ κ`) whose
survival functions `t ↦ κ x {t < y}` are monotone in `x`, instead of a condition at every real
`x` on Mathlib's specific `condDistrib` version, whose values off the support of `X̂` are
construction-dependent. -/
theorem convex_order_martingale_coupling_iff_v2 {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXint : Integrable X μ) (hYint : Integrable Y ν) :
    ConvexOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] =ᵐ[ρ] Xhat ∧
        ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧
          ρ.map (fun ω => (Xhat ω, Yhat ω)) = (ρ.map Xhat) ⊗ₘ κ ∧
          ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ, κ x₁ {y : ℝ | t < y} ≤ κ x₂ {y : ℝ | t < y} := by sorry

end StochasticOrders.Convex
