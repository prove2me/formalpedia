-- Prove2me | Theorems.Thm_Problem97_CGN_capPairApexes_mem_edgeAt_packet
-- name    : Problem97.CGN.capPairApexes_mem_edgeAt_packet
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:48:25.38956+00:00
-- url     : https://prove2.me/theorems/ad36a011-acb4-4179-9347-e446308dc071
-- title:
--   Unpack Membership in the Apex Set of a Cap Edge
-- statement:
--   If a point a belongs to the apex set associated with the cap edge joining L(r) and L(s), then a lies in A, differs from both endpoints, and has equal distance to the two endpoints.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_capPairApexes_mem_edgeAt_packet.lean#L1-L102

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN by Stage 2 proof cut; source SHA-256 9f1ccd7df30637d7fbdf412fb40177dedb5193c45ec2993df86f137cbd34ffb7 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_Dumitrescu_L6
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

theorem Problem97.CGN.capPairApexes_mem_edgeAt_packet {m : ℕ} {L : OrderedCap m}
    {A : Finset ℝ²} {r s : Fin m} {a : ℝ²}
    (ha : a ∈ Problem97.Dumitrescu.capPairApexes A (edgeAt L r s)) :
    a ∈ A ∧ a ≠ L.points r ∧ a ≠ L.points s ∧
      dist a (L.points r) = dist a (L.points s) := by sorry
