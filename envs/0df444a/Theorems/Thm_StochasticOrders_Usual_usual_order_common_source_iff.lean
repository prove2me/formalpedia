-- Prove2me | Theorems.Thm_StochasticOrders_Usual_usual_order_common_source_iff
-- name    : StochasticOrders.Usual.usual_order_common_source_iff
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:44.127792+00:00
-- url     : https://prove2.me/theorems/3f3a5e5f-9dca-4375-b833-8d072c6e98fc
-- title:
--   Theorem 1.A.2 — common-random-source characterization
-- statement:
--   Let $X$ on $(\Omega,\mu)$ and $Y$ on $(\Omega',\nu)$ be real-valued random variables. Then
--   $X \le_{st} Y$ if, and only if, there exist a random variable $Z$ (valued in an arbitrary
--   measurable space $S$) and functions $\psi_1,\psi_2 : S \to \mathbb{R}$ such that
--   $\psi_1(z) \le \psi_2(z)$ for every $z \in S$, and
--
--   $$X =_{st} \psi_1(Z), \qquad Y =_{st} \psi_2(Z).$$
--
--   This restates Theorem 1.A.1 with the roles reversed: instead of coupling $X$ and $Y$ directly,
--   both are represented as increasing-in-a-fixed-sense images of one common random source $Z$.
--   The book notes this equivalence has an "obvious" proof from Theorem 1.A.1 and omits it; it is
--   included as a milestone because it is the same construction stated the other way, and is used
--   directly to build the goal's coupling from a common uniform source.
--
--   **Formalization Note** $Z$'s codomain $S$ is left an arbitrary measurable space (matching the
--   book's unrestricted "random variable $Z$"), realized as a random variable on a probability
--   space $(\Omega'',\rho)$; $\psi_1(Z)=_{st}X$ is `IdentDistrib (ψ1 ∘ Z) X ρ μ`.
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
arbitrary measurable space `S`, matching the book's unrestricted "random variable Z". -/
theorem usual_order_common_source_iff {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) :
    UsualOrder μ ν X Y ↔
      ∃ (S : Type) (_ : MeasurableSpace S) (Ω'' : Type) (_ : MeasurableSpace Ω'')
        (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ) (Z : Ω'' → S) (ψ1 ψ2 : S → ℝ),
        (∀ s : S, ψ1 s ≤ ψ2 s) ∧
        IdentDistrib (ψ1 ∘ Z) X ρ μ ∧ IdentDistrib (ψ2 ∘ Z) Y ρ ν := by sorry

end StochasticOrders.Usual
