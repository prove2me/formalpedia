-- Prove2me | Theorems.Thm_StochasticOrders_MonotoneConvex_icv_supermartingale_coupling_iff_v2
-- name    : StochasticOrders.MonotoneConvex.icv_supermartingale_coupling_iff_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:19.877362+00:00
-- url     : https://prove2.me/theorems/86823cca-92cd-444b-995e-1453ec4b15b7
-- title:
--   Theorem 4.A.5 (increasing concave case) — supermartingale-coupling characterization of the increasing concave order (corrected: finite means, random variables)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be random variables with finite means (measurable and integrable, the standing assumption of Chapters 3–4). Then
--
--   $$X \le_{icv} Y \iff \exists\,(\Omega'',\rho),\ \hat X,\hat Y:\Omega''\to\mathbb{R} \text{ random variables with } \hat X =_{st} X,\ \hat Y =_{st} Y,\ \text{and } \{\hat Y,\hat X\} \text{ a supermartingale},$$
--
--   i.e. $E[\hat X \mid \hat Y] \le \hat Y$ a.s. — note the *swapped* roles of $\hat X$ and $\hat Y$ in the conditioning relative to the increasing convex case. **Furthermore**, $\hat X$ and $\hat Y$ can be selected such that $[\hat X \mid \hat Y = y]$ is increasing in $y$ in the usual stochastic order $\le_{st}$. This is the companion half of Theorem 4.A.5 (apply the increasing convex case to $-Y$, $-X$).
--
--   **Formalization Note.** The retired version let $X$, $Y$ be arbitrary functions, so a non-measurable $X$ satisfied $X \le_{icv} X$ reflexively while no identically distributed copy existed, and the forward direction was refuted; it also assumed no integrability, so Mathlib's conditional expectation of a non-integrable $\hat X$ would be the junk value $0$. The new statement requires $X$, $Y$, $\hat X$, $\hat Y$ to be measurable (random variables) and makes the standing finite-mean assumption explicit (`Integrable X μ`, `Integrable Y ν`); `Measurable Ŷ` is moreover what makes $\sigma(\hat Y)$ a sub-σ-algebra of the ambient one, without which Mathlib's `ρ[X̂ | σ(Ŷ)]` is $0$ (`condExp_of_not_le`). The supermartingale condition is `ρ[X̂ | MeasurableSpace.comap Ŷ _] ≤ᵐ[ρ] Ŷ`. The book's "$[\hat X\mid\hat Y = y]$ increasing in $y$" is formalized as the existence of a Markov kernel $\kappa$ with $\rho\circ(\hat Y,\hat X)^{-1} = (\rho\circ\hat Y^{-1})\otimes\kappa$ whose survival functions are monotone in $y$ at every threshold (a version of the conditional law, which is what the book's statement can mean), instead of a condition at every real $y$ on Mathlib's specific `condDistrib` version, whose values off the support of $\hat Y$ are construction-dependent. The increasing concave order is the imported `IcvOrder`, equivalent for integrable $X$, $Y$ to the book's definition. Conventions made explicit: random variables are measurable functions on probability spaces (the book's standing convention, stated as `Measurable` hypotheses and `IsProbabilityMeasure` instances); "$=_{st}$" is `ProbabilityTheory.IdentDistrib`; the common space $(\Omega'',\rho)$ is existentially quantified, and the coupled copies are themselves random variables. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 183, Theorem 4.A.5

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory ProbabilityTheory

/-- Theorem 4.A.5 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 183), increasing
concave case: for random variables `X`, `Y` with finite means, `X ≤icv Y` if, and only if, there
exist two random variables `X̂` and `Ŷ`, defined on the same probability space, such that
`X̂ =st X`, `Ŷ =st Y`, and `{Ŷ, X̂}` is a supermartingale, that is, `E[X̂ | Ŷ] ≤ Ŷ` a.s. (note
the swapped roles of `X̂` and `Ŷ` in the conditioning relative to the increasing convex case).
Furthermore, `X̂` and `Ŷ` can be selected such that `[X̂ | Ŷ = y]` is increasing in `y` in the
usual stochastic order `≤st`.

Corrected version (`_v2`) of `icv_supermartingale_coupling_iff`: (1) `X`, `Y`, `X̂`, `Ŷ` are
random variables (`Measurable`); the retired statement let `X` be non-measurable, so
`IcvOrder μ μ X X` held while no `IdentDistrib` copy existed; `Measurable Ŷ` is also what makes
the conditional expectation `ρ[X̂ | comap Ŷ]` meaningful (`condExp_of_not_le`). (2) the standing
finite-mean assumption of Chapters 3–4 is explicit (`Integrable X μ`, `Integrable Y ν`), without
which `ρ[X̂ | ·]` is Mathlib's junk `0` for a non-integrable `X̂`. (3) the "Furthermore" clause is
stated as the existence of a Markov kernel `κ` disintegrating the joint law
(`ρ.map (Ŷ, X̂) = ρ.map Ŷ ⊗ₘ κ`) whose survival functions are monotone in the conditioning
value, rather than a condition at every real `y` on Mathlib's specific `condDistrib` version. -/
theorem icv_supermartingale_coupling_iff_v2 {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXint : Integrable X μ) (hYint : Integrable Y ν) :
    IcvOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Xhat | MeasurableSpace.comap Yhat inferInstance] ≤ᵐ[ρ] Yhat ∧
        ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧
          ρ.map (fun ω => (Yhat ω, Xhat ω)) = (ρ.map Yhat) ⊗ₘ κ ∧
          ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ → ∀ t : ℝ, κ y₁ {x : ℝ | t < x} ≤ κ y₂ {x : ℝ | t < x} := by sorry

end StochasticOrders.MonotoneConvex
