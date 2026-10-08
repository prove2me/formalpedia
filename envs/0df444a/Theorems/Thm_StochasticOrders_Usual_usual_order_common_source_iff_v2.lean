-- Prove2me | Theorems.Thm_StochasticOrders_Usual_usual_order_common_source_iff_v2
-- name    : StochasticOrders.Usual.usual_order_common_source_iff_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:31.338328+00:00
-- url     : https://prove2.me/theorems/c3d8ffa2-0f68-4d52-b514-6d67a57e5e24
-- title:
--   Theorem 1.A.2 — common-random-source characterization of the usual stochastic order (corrected: random variables)
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be real-valued random variables (measurable functions on probability spaces). Then $X \le_{st} Y$ if, and only if, there exist a random variable $Z$ (valued in an arbitrary measurable space $S$) and measurable functions $\psi_1,\psi_2 : S \to \mathbb{R}$ such that $\psi_1(z) \le \psi_2(z)$ for every $z \in S$, and
--
--   $$X =_{st} \psi_1(Z), \qquad Y =_{st} \psi_2(Z).$$
--
--   This restates Theorem 1.A.1 with the roles reversed: instead of coupling $X$ and $Y$ directly, both are represented as ordered images of one common random source $Z$. The book notes that the equivalence follows at once from Theorem 1.A.1 (take $Z = U$ uniform and $\psi_1 = F^{-1}$, $\psi_2 = G^{-1}$).
--
--   **Formalization Note.** The retired version let $X$ and $Y$ be arbitrary functions, so a non-measurable $X$ satisfied $X \le_{st} X$ while no identically distributed representation $\psi_1(Z)$ of it could exist (`IdentDistrib` contains a.e.-measurability), and the forward direction was refuted. The new statement adds `Measurable X`, `Measurable Y`; the common source $Z$ is a random variable (`Measurable Z`) and $\psi_1$, $\psi_2$ are measurable, so that $\psi_1(Z)$, $\psi_2(Z)$ are the random variables the book's "$=_{st}$" presupposes. $S$ is left an arbitrary measurable space, matching the book's unrestricted "random variable $Z$". Conventions made explicit: random variables are measurable functions on probability spaces (the book's standing convention, stated as `Measurable` hypotheses and `IsProbabilityMeasure` instances); "$=_{st}$" is `ProbabilityTheory.IdentDistrib`; the common space $(\Omega'',\rho)$ is existentially quantified, and the coupled copies are themselves random variables. No correction to the printed source.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 5, Theorem 1.A.2

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

namespace StochasticOrders.Usual

open MeasureTheory ProbabilityTheory

/-- Theorem 1.A.2 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 5): two random
variables `X` and `Y` satisfy `X ≤st Y` if, and only if, there exist a random variable `Z` and
functions `ψ1` and `ψ2` such that `ψ1(z) ≤ ψ2(z)` for all `z` and `X =st ψ1(Z)` and `Y =st ψ2(Z)`.
`Z` is formalized as a random variable on a probability space `(Ω'', ρ)` taking values in an
arbitrary measurable space `S`, matching the book's unrestricted "random variable Z".

Corrected version (`_v2`) of `usual_order_common_source_iff`: the retired statement let `X`, `Y`
be arbitrary functions, so a non-measurable `X` satisfied `UsualOrder μ μ X X` while no
`IdentDistrib` representation of it exists. "Random variable" is now carried by `Measurable X`,
`Measurable Y`; the common source `Z` is a random variable and `ψ1`, `ψ2` are measurable, so that
`ψ1(Z)`, `ψ2(Z)` are random variables as the book's `=st` presupposes. -/
theorem usual_order_common_source_iff_v2 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    UsualOrder μ ν X Y ↔
      ∃ (S : Type) (_ : MeasurableSpace S) (Ω'' : Type) (_ : MeasurableSpace Ω'')
        (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ) (Z : Ω'' → S) (ψ1 ψ2 : S → ℝ),
        Measurable Z ∧ Measurable ψ1 ∧ Measurable ψ2 ∧
        (∀ s : S, ψ1 s ≤ ψ2 s) ∧
        IdentDistrib (ψ1 ∘ Z) X ρ μ ∧ IdentDistrib (ψ2 ∘ Z) Y ρ ν := by sorry

end StochasticOrders.Usual
