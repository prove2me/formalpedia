-- Prove2me | Theorems.Thm_StochasticOrders_Usual_usual_order_coupling_iff_v2
-- name    : StochasticOrders.Usual.usual_order_coupling_iff_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:43.700981+00:00
-- url     : https://prove2.me/theorems/85924196-7d5d-4c97-9b79-e5207ff7641b
-- title:
--   Theorem 1.A.1 — coupling characterization of the usual stochastic order (corrected: random variables)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be real-valued random variables, i.e. measurable functions on probability spaces. Then
--
--   $$X \le_{st} Y \iff \exists\, (\Omega'',\rho),\ \hat X, \hat Y : \Omega'' \to \mathbb{R}\ \text{random variables such that } \hat X =_{st} X,\ \hat Y =_{st} Y,\ \text{and } P\{\hat X \le \hat Y\} = 1.$$
--
--   This is the book's Strassen-type coupling characterization of $\le_{st}$: the order between two distributions holds exactly when a copy of each can be built on a *common* probability space so that, with probability one, the copy of $X$ never exceeds the copy of $Y$. The proof exhibits the explicit construction $\hat X = F^{-1}(U)$, $\hat Y = G^{-1}(U)$ for a single uniform $[0,1]$ random variable $U$.
--
--   **Formalization Note.** The retired version let $X$ and $Y$ be arbitrary functions, so a non-measurable $X$ satisfied $X \le_{st} X$ (the tail inequalities are reflexive even for outer measures) while no identically distributed copy of it could exist (`IdentDistrib` contains a.e.-measurability), and the forward direction was refuted. The new statement adds `Measurable X`, `Measurable Y`, and requires the coupled copies $\hat X$, $\hat Y$ to be measurable, as "random variables" means. Conventions made explicit: random variables are measurable functions on probability spaces (the book's standing convention, stated as `Measurable` hypotheses and `IsProbabilityMeasure` instances); "$=_{st}$" is `ProbabilityTheory.IdentDistrib`; the common space $(\Omega'',\rho)$ is existentially quantified, and the coupled copies are themselves random variables. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 5, Theorem 1.A.1

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

namespace StochasticOrders.Usual

open MeasureTheory ProbabilityTheory

/-- Theorem 1.A.1 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 5): two random
variables `X` and `Y` satisfy `X ≤st Y` if, and only if, there exist two random variables `X̂` and
`Ŷ`, defined on the same probability space, such that `X̂ =st X`, `Ŷ =st Y`, and
`P{X̂ ≤ Ŷ} = 1`.

Corrected version (`_v2`) of `usual_order_coupling_iff`: the retired statement let `X`, `Y` be
arbitrary functions, so a non-measurable `X` satisfied `UsualOrder μ μ X X` while no
`IdentDistrib` copy of it exists. "Random variable" is now carried by `Measurable X`,
`Measurable Y`, and the coupled copies `X̂`, `Ŷ` are random variables as well. -/
theorem usual_order_coupling_iff_v2 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    UsualOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧ ρ {ω | Xhat ω ≤ Yhat ω} = 1 := by sorry

end StochasticOrders.Usual
