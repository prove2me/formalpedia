-- Prove2me | Theorems.Thm_StochasticOrders_Multivariate_multivariate_order_conjunction
-- name    : StochasticOrders.Multivariate.multivariate_order_conjunction
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:09:07.041774+00:00
-- url     : https://prove2.me/theorems/fc28449d-c045-406f-9b51-aa3c51c2ab58
-- title:
--   Theorem 6.B.16(b) — closure of the usual multivariate stochastic order under conjunctions
-- statement:
--   Let $X_1,\dots,X_m$ be a set of independent random vectors where the dimension of $X_i$ is
--   $k_i$, and let $Y_1,\dots,Y_m$ be another set of independent random vectors, with $Y_i$ also
--   of dimension $k_i$, $i=1,\dots,m$. Denote $k=k_1+\cdots+k_m$. If $X_i \le_{st} Y_i$ for every
--   $i$, then for any increasing function $\psi:\mathbb{R}^k\to\mathbb{R}$,
--
--   $$\psi(X_1,\dots,X_m) \le_{st} \psi(Y_1,\dots,Y_m).$$
--
--   That is, the usual multivariate stochastic order is closed under conjunctions; in particular
--   (taking $\psi$ to be a coordinatewise sum) it is closed under convolutions. Note that $\psi$'s
--   codomain is $\mathbb{R}$, so the conclusion's $\le_{st}$ is genuinely the *univariate* usual
--   stochastic order applied to the two real-valued random variables $\psi(X_1,\dots,X_m)$ and
--   $\psi(Y_1,\dots,Y_m)$, even though the inputs are vector-valued. The book notes that parts (a)
--   (image under an increasing map) and (c) (marginalization) of Theorem 6.B.16 are both special
--   cases of this part (b).
--
--   **Formalization Note** The book allows a different dimension $k_i$ per $i$; this mission
--   drafts the case of a common dimension $n$ across all $X_i,Y_i$ (so the concatenated input
--   lives in `Fin m → Fin n → ℝ`, itself carrying the coordinatewise order Mathlib gives nested
--   `Pi` types, matching $\mathbb{R}^{mn}$'s coordinatewise order) — the "closed under
--   convolutions" special case the book itself names, chosen to avoid a dependent-sum
--   concatenation of vectors of genuinely different lengths for a mission of this size; the
--   general varying-dimension statement is left for a future pass (see `STATUS.md`). The
--   conclusion is stated directly as the univariate order's own defining inequality
--   ($\forall x,\ \mu\{x < \psi(X_\bullet)\} \le \nu\{x < \psi(Y_\bullet)\}$), restated locally
--   rather than importing Chunk 01's `UsualOrder`, since drafts cannot import another mission's
--   definitions.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 273, Theorem 6.B.16(b)

import Mathlib
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder

namespace StochasticOrders.Multivariate

open MeasureTheory ProbabilityTheory

/-- Theorem 6.B.16(b) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 273): let
`X 1, …, X m` be independent `n`-dimensional random vectors and `Y 1, …, Y m` another independent
family of `n`-dimensional random vectors (the book allows a different dimension `k_i` per `i`;
here all vectors share a common dimension `n`, the "convolution" special case the book itself
names). If `X i ≤st Y i` for every `i`, then for any increasing function
`ψ : (Fin m → Fin n → ℝ) → ℝ`, `ψ(X 1, …, X m) ≤st ψ(Y 1, …, Y m)` in the *univariate* usual
stochastic order (the book's `ψ` has codomain `ℝ`, so this closure statement is genuinely
univariate even though its inputs are vector-valued) — restated locally rather than imported,
since drafts cannot import another mission's definitions (Chunk 01's `UsualOrder`). -/
theorem multivariate_order_conjunction {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m n : ℕ} (X : Fin m → Ω → Fin n → ℝ) (Y : Fin m → Ω' → Fin n → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, MultivariateOrder μ ν (X i) (Y i))
    (ψ : (Fin m → Fin n → ℝ) → ℝ) (hψ : Monotone ψ) :
    ∀ x : ℝ, μ {ω | x < ψ (fun i => X i ω)} ≤ ν {ω | x < ψ (fun i => Y i ω)} := by sorry

end StochasticOrders.Multivariate
