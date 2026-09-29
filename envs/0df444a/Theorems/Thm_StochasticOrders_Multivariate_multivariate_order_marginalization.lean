-- Prove2me | Theorems.Thm_StochasticOrders_Multivariate_multivariate_order_marginalization
-- name    : StochasticOrders.Multivariate.multivariate_order_marginalization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:09:35.102671+00:00
-- url     : https://prove2.me/theorems/80bac15e-d16a-4ca8-846e-bebf511ffad6
-- title:
--   Theorem 6.B.16(c) — closure of the usual multivariate stochastic order under marginalization
-- statement:
--   Let $X=(X_1,\dots,X_n)$ and $Y=(Y_1,\dots,Y_n)$ be two $n$-dimensional random vectors. If
--   $X \le_{st} Y$, then $X_I \le_{st} Y_I$ for each $I \subseteq \{1,\dots,n\}$, where $X_I$
--   denotes the sub-vector of $X$ indexed by $I$. That is, the usual multivariate stochastic order
--   is closed under marginalization — a special case of part (b) (Theorem 6.B.16(b), taking
--   $\psi$ to be the coordinate projection onto $I$).
--
--   **Formalization Note** $I\subseteq\{1,\dots,n\}$ of size $k$ is encoded as an injective
--   reindexing $r : \text{Fin } k \to \text{Fin } n$, and $X_I$, $Y_I$ as $X$, $Y$ precomposed
--   coordinatewise with $r$ (`fun ω i => X ω (r i)`), matching the book's subvector notation
--   (6.A.1) exactly.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 273, Theorem 6.B.16(c)

import Mathlib
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder

namespace StochasticOrders.Multivariate

open MeasureTheory ProbabilityTheory

/-- Theorem 6.B.16(c) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 273): let
`X = (X_1, …, X_n)` and `Y = (Y_1, …, Y_n)` be `n`-dimensional random vectors. If `X ≤st Y`, then
`X_I ≤st Y_I` for each `I ⊆ {1, …, n}`: the usual multivariate stochastic order is closed under
marginalization. `I` is encoded as an injective reindexing `r : Fin k → Fin n` (`k = |I|`), and
`X_I`, `Y_I` as `X`, `Y` precomposed coordinatewise with `r`. -/
theorem multivariate_order_marginalization {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n k : ℕ} (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ) (hord : MultivariateOrder μ ν X Y)
    (r : Fin k → Fin n) (hr : Function.Injective r) :
    MultivariateOrder μ ν (fun ω i => X ω (r i)) (fun ω i => Y ω (r i)) := by sorry

end StochasticOrders.Multivariate
