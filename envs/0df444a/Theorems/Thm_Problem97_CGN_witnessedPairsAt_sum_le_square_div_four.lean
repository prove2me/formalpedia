-- Prove2me | Theorems.Thm_Problem97_CGN_witnessedPairsAt_sum_le_square_div_four
-- name    : Problem97.CGN.witnessedPairsAt_sum_le_square_div_four
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:02:45.823836+00:00
-- url     : https://prove2.me/theorems/1e926cfe-d471-42f2-a5e8-1e96e756c5eb
-- title:
--   Total cap-witness matching bound
-- statement:
--   Let $L=(p_0,\ldots,p_{m-1})$ be an ordered cap. Assume that, for each apex position $j$, witnessed pairs have at most one right endpoint for each left endpoint and at most one left endpoint for each right endpoint. Then the total number of witnessed pairs, summed over all apex positions, is at most $$\left\lfloor\frac{(m-1)^2}{4}\right\rfloor.$$ This is the matching-count shell used after the geometric cap-witness uniqueness lemmas.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_witnessedPairsAt_sum_le_square_div_four.lean#L1-L102

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN by Stage 2 proof cut; source SHA-256 9f1ccd7df30637d7fbdf412fb40177dedb5193c45ec2993df86f137cbd34ffb7 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin
open Problem97 Problem97.CGN



/-!
# CGN7: indexed cap-side witness matching scaffold

This file records the CGN7-local indexed witness relation requested by the
updated counterexample-card-ge-nine prose.  The geometry that produces the
one-sided injectivity hypotheses lives in the CGN6 lemmas; this module only
packages the ordered-cap interface and the partial-matching counting shell.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open Finset








variable {m : ℕ}

theorem Problem97.CGN.witnessedPairsAt_sum_le_square_div_four {m : ℕ} (L : OrderedCap m)
    (hleft : ∀ j : Fin m, ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j r t → s = t)
    (hright : ∀ j : Fin m, ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j t s → r = t) :
    ∑ j : Fin m, (WitnessedPairsAt L j).card ≤ (m - 1)^2 / 4 := by sorry
