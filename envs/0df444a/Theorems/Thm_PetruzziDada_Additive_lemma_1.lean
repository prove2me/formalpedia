-- Prove2me | Theorems.Thm_PetruzziDada_Additive_lemma_1
-- name    : PetruzziDada.Additive.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:08.297813+00:00
-- url     : https://prove2.me/theorems/8786ff44-6abd-49d7-b109-9a971dabc2f4
-- title:
--   Lemma 1 — for a fixed z the optimal price is uniquely p(z) = p⁰ − Θ(z)/2b
-- statement:
--   In the additive-demand price-setting newsvendor, let $p^0 = (a + bc + \mu)/2b$ be the riskless price and $\Theta(z) = \int_z^B (u-z) f(u)\,du$ the expected shortages. For every real stocking factor $z$, the price
--   $$p(z) = p^0 - \frac{\Theta(z)}{2b}$$
--   maximizes $p \mapsto E[\Pi(z,p)]$ over all real prices,
--   $$E[\Pi(z,p)] \le E[\Pi(z,p(z))] \quad \text{for every } p \in \mathbb R,$$
--   and it is the only maximizer: if $E[\Pi(z,p)] = E[\Pi(z,p(z))]$ then $p = p(z)$.
--
--   This is Lemma 1 of the paper. It reduces the joint pricing and stocking problem (4) to a one-dimensional problem in $z$, the maximization of $E[\Pi(z,p(z))]$.
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, p. 185, Lemma 1

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory

namespace PetruzziDada.Additive

/-- Lemma 1, p. 185: for a fixed `z` the optimal price is determined uniquely,
`p* = p(z) = p⁰ - Θ(z)/2b`: it maximizes `p ↦ E[Π(z, p)]` over all real prices, and it is the
only maximizer. -/
theorem lemma_1 (M : Model) (z : ℝ) :
    (∀ p : ℝ, M.expProfit z p ≤ M.expProfit z (M.price z)) ∧
      ∀ p : ℝ, M.expProfit z p = M.expProfit z (M.price z) → p = M.price z := by sorry
end PetruzziDada.Additive
