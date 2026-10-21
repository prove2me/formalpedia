-- Prove2me | Theorems.Thm_PetruzziDada_Additive_theorem_1a
-- name    : PetruzziDada.Additive.theorem_1a
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:12.836855+00:00
-- url     : https://prove2.me/theorems/73886a8c-897e-4c15-b39f-decd340922f8
-- title:
--   Theorem 1(a) — for an arbitrary distribution, an exhaustive search over z ∈ [A, B] determines z*
-- statement:
--   In the additive-demand price-setting newsvendor with an arbitrary density $f$ on $[A,B]$ (subject only to the standing assumptions), let $p(z) = p^0 - \Theta(z)/2b$ be the price rule of Lemma 1. Then:
--
--   1. the reduced objective $z \mapsto E[\Pi(z,p(z))]$ attains its maximum over $[A,B]$ at some $z^* \in [A,B]$; and
--   2. every such maximizer $z^*$, sold at $p^* = p(z^*)$, solves the joint problem (4) over the region:
--   $$E[\Pi(z,p)] \le E[\Pi(z^*,p(z^*))] \quad \text{for all } z \in [A,B] \text{ and all } p \in \mathbb R.$$
--
--   This is Theorem 1(a): an exhaustive search over $z$ in $[A,B]$ determines the optimal policy $q^* = y(p^*) + z^*$, $p^* = p(z^*)$.
--
--   **Formalization Note** "Arbitrary distribution function" is read within the paper's density setting: $\varepsilon$ has a density on $[A,B]$. "Will determine $z^*$" is rendered as existence of a maximizer of the reduced objective over $[A,B]$ together with joint optimality of every such maximizer over $z \in [A,B]$ and all real prices.
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, p. 185, Theorem 1(a)

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory

namespace PetruzziDada.Additive

/-- Theorem 1(a), p. 185: for an arbitrary distribution (here: an arbitrary density on
`[A, B]`), an exhaustive search of `z ↦ E[Π(z, p(z))]` over `[A, B]` determines `z*`: a maximizer
exists, and every maximizer `z*`, priced at `p* = p(z*)`, is optimal for the joint problem (4) over
`z ∈ [A, B]` and every real price `p`. -/
theorem theorem_1a (M : Model) :
    (∃ zstar ∈ Set.Icc M.A M.B, IsMaxOn M.reducedProfit (Set.Icc M.A M.B) zstar) ∧
      ∀ zstar ∈ Set.Icc M.A M.B, IsMaxOn M.reducedProfit (Set.Icc M.A M.B) zstar →
        ∀ z ∈ Set.Icc M.A M.B, ∀ p : ℝ, M.expProfit z p ≤ M.expProfit zstar (M.price zstar) := by sorry
end PetruzziDada.Additive
