-- Prove2me | Theorems.Thm_Problem97_CGN_card_witnessedPairsAt_le_right
-- name    : Problem97.CGN.card_witnessedPairsAt_le_right
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:49:18.370279+00:00
-- url     : https://prove2.me/theorems/2e5d8fbb-a320-4f25-a91a-1cc76618d487
-- title:
--   Right-Side Bound for Cap Edges Witnessed at One Vertex
-- statement:
--   Fix a vertex j of an ordered cap with m vertices. If, for every later endpoint s, two witnessed cap edges ending at s through j must have the same earlier endpoint, then the number of cap-index pairs witnessed at j is at most m − 1 − j.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_card_witnessedPairsAt_le_right.lean#L1-L100

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

theorem Problem97.CGN.card_witnessedPairsAt_le_right {m : ℕ} (L : OrderedCap m) (j : Fin m)
    (hright : ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j t s → r = t) :
    (WitnessedPairsAt L j).card ≤ m - 1 - j.val := by sorry
