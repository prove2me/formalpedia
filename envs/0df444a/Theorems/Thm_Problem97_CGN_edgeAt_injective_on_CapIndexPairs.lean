-- Prove2me | Theorems.Thm_Problem97_CGN_edgeAt_injective_on_CapIndexPairs
-- name    : Problem97.CGN.edgeAt_injective_on_CapIndexPairs
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:47:54.088016+00:00
-- url     : https://prove2.me/theorems/973616c3-a714-4b4f-8337-53e8523b8582
-- title:
--   Ordered Cap Edges Determine Their Index Pairs
-- statement:
--   For an ordered cap L, two oriented index pairs r < s and u < v that determine the same unordered two-vertex edge must be the same ordered pair of indices.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_edgeAt_injective_on_CapIndexPairs.lean#L1-L100

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

theorem Problem97.CGN.edgeAt_injective_on_CapIndexPairs {m : ℕ} {L : OrderedCap m}
    {p q : Fin m × Fin m} (hp : p ∈ CapIndexPairs m) (hq : q ∈ CapIndexPairs m)
    (heq : edgeAt L p.1 p.2 = edgeAt L q.1 q.2) :
    p = q := by sorry
