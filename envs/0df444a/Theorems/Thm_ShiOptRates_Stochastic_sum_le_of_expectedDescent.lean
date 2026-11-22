-- Prove2me | Theorems.Thm_ShiOptRates_Stochastic_sum_le_of_expectedDescent
-- name    : ShiOptRates.Stochastic.sum_le_of_expectedDescent
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-08T22:30:05.817545+00:00
-- url     : https://prove2.me/theorems/1899b8af-bd54-4946-899c-d57fe85bf578
-- title:
--   Telescoping the expected-descent recursion: $\tfrac{h}{2}\sum_{k<K} b_k \le (a_0 - a_K) + K L h^{2}\sigma^{2}/2$
-- statement:
--   Let $(a_k)_{k\in\mathbb{N}}$ and $(b_k)_{k\in\mathbb{N}}$ be real sequences, and let $h$, $L$, $\sigma$ be reals and $K \in \mathbb{N}$. Assume $(a, b)$ satisfies the **expected-descent recursion** with data $(h, L, \sigma, K)$, that is
--
--   $$
--   a_{k+1} \;\le\; a_k - \frac{h}{2}\, b_k + \frac{L\,h^{2}\sigma^{2}}{2}
--   \qquad \text{for all } k < K .
--   $$
--
--   Summing this inequality over $k = 0, \dots, K-1$ and telescoping the $a$-terms gives
--
--   $$
--   \frac{h}{2}\sum_{k=0}^{K-1} b_k \;\le\; (a_0 - a_K) \;+\; K\cdot\frac{L\,h^{2}\sigma^{2}}{2} .
--   $$
--
--   In the intended reading $a_k = \mathbb{E} f(x_k)$ and $b_k = \mathbb{E}\lVert \nabla f(x_k)\rVert^{2}$ along stochastic gradient descent with stepsize $h$ on an $L$-smooth objective with gradient-noise second moment $\sigma^{2}$: the total gradient mass accumulated over the run is paid for by the objective decrease $a_0 - a_K$ plus $K$ copies of the per-step noise penalty. Dividing by $K$ turns this into the standard two-term bound on $\min_{k<K} b_k$, and thence into the $\varepsilon^{-4}$ complexity of SGD. The step is deliberately isolated as a purely arithmetic lemma about two real sequences, so that the explicit constants downstream are visibly independent of any probabilistic machinery — no lower bound on $a_K$, no positivity of $h$, and no measure-theoretic hypothesis is needed here.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Recursion.lean#L50-L70 (commit 4c0b84980914...) | Formalized in lean-optrates by Yueheng Shi. Original file licensed under the Apache License 2.0; the platform copy was produced by declaration-graph skeleton subtraction and the root namespace `OptRates` was renamed to `ShiOptRates`. No statement or proof was otherwise altered.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Recursion.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; the proof is replaced by `sorry`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiOptrates_Cost
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_ShiOptrates_Stochastic_Recursion
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L3a — The expected-descent recursion

The part of the classical SGD analysis that is *not* probabilistic.  Every
expectation-based rate proof for a first-order method passes through a scalar recursion of
the form

`aₖ₊₁ ≤ aₖ - (h/2) bₖ + L h² σ² / 2`

where `aₖ = E f(xₖ)` and `bₖ = E‖∇f(xₖ)‖²`.  Establishing that recursion is the
probabilistic step (`Optrates.Stochastic.OneStep`); turning it into a rate is real
analysis, and is done here once.

Separating the two is what makes the `ε⁻⁴` bound auditable: the constant `8 L Δ₀ σ² / ε⁴`
below is a consequence of arithmetic on the recursion alone, and no martingale theory can
change it.

## Main results

* `sum_le_of_expectedDescent` — telescoping the recursion.
* `exists_le_of_expectedDescent` — `min_{k<K} bₖ ≤ 2Δ₀/(hK) + L h σ²`, the standard
  two-term bound with both terms explicit.
* `exists_le_sq_of_stepsize` — **GL3's arithmetic core**: at `h = ε²/(2Lσ²)` and
  `K ≥ 8 L Δ₀ σ² / ε⁴` some `bₖ ≤ ε²`.  Stepsize supplied and verified, not derived, per
  the library's convention.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open Finset

variable {a b : ℕ → ℝ} {h L σ : ℝ} {K : ℕ}

theorem ShiOptRates.Stochastic.sum_le_of_expectedDescent (hrec : ExpectedDescent a b h L σ K) :
    h / 2 * ∑ k ∈ range K, b k ≤ (a 0 - a K) + K * (L * h ^ 2 * σ ^ 2 / 2) := by sorry
