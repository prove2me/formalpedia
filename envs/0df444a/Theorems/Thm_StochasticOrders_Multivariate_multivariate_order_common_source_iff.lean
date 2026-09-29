-- Prove2me | Theorems.Thm_StochasticOrders_Multivariate_multivariate_order_common_source_iff
-- name    : StochasticOrders.Multivariate.multivariate_order_common_source_iff
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:08:36.376167+00:00
-- url     : https://prove2.me/theorems/947cb63b-7664-4b57-9ffb-270f2b476712
-- title:
--   Theorem 6.B.2 — common-source characterization of the usual multivariate stochastic order
-- statement:
--   The $n$-dimensional random vectors $X$ and $Y$ satisfy $X \le_{st} Y$ if, and only if, there
--   exist a random variable $Z$ and $\mathbb{R}^n$-valued functions $\psi_1$ and $\psi_2$ such
--   that $\psi_1(z) \le \psi_2(z)$ (coordinatewise) for all $z \in \mathbb{R}$, and
--   $X =_{st} \psi_1(Z)$ and $Y =_{st} \psi_2(Z)$. This is the multivariate analogue of Theorem
--   1.A.2 (Chunk 01's own coupling companion), an immediate restatement of Theorem 6.B.1.
--
--   **Formalization Note** The book's "random variable $Z$" is explicitly quantified over
--   $z \in \mathbb{R}$ in the inequality $\psi_1(z)\le\psi_2(z)$, so $Z$ is drafted as
--   $\mathbb{R}$-valued (not an arbitrary-type "common source", unlike some other common-source
--   theorems in this series). $\psi_1,\psi_2 : \mathbb{R} \to (\text{Fin } n \to \mathbb{R})$ are
--   genuine functions, and "$X =_{st}\psi_1(Z)$" is `IdentDistrib (ψ1 ∘ Z) X`.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 267, Theorem 6.B.2

import Mathlib
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder

namespace StochasticOrders.Multivariate

open MeasureTheory ProbabilityTheory

/-- Theorem 6.B.2 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 267): the
`n`-dimensional random vectors `X` and `Y` satisfy `X ≤st Y` if, and only if, there exist a
real-valued random variable `Z` and `Fin n → ℝ`-valued functions `ψ1` and `ψ2` such that
`ψ1 z ≤ ψ2 z` (coordinatewise) for all `z ∈ ℝ`, and `X =st ψ1 ∘ Z` and `Y =st ψ2 ∘ Z`. -/
theorem multivariate_order_common_source_iff {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) :
    MultivariateOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Z : Ω'' → ℝ) (ψ1 ψ2 : ℝ → Fin n → ℝ),
        (∀ z : ℝ, ψ1 z ≤ ψ2 z) ∧
        IdentDistrib (ψ1 ∘ Z) X ρ μ ∧ IdentDistrib (ψ2 ∘ Z) Y ρ ν := by sorry

end StochasticOrders.Multivariate
