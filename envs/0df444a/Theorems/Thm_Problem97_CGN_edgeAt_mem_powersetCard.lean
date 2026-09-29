-- Prove2me | Theorems.Thm_Problem97_CGN_edgeAt_mem_powersetCard
-- name    : Problem97.CGN.edgeAt_mem_powersetCard
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:47:23.6157+00:00
-- url     : https://prove2.me/theorems/5833cf03-2f86-4a13-951e-108cf442abc6
-- title:
--   An Oriented Cap Edge Is a Two-Element Subset
-- statement:
--   If every vertex of an ordered cap L lies in a finite set A and r < s, then the unordered edge formed by L(r) and L(s) is a two-element subset of A, hence belongs to the two-element powerset of A.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_edgeAt_mem_powersetCard.lean#L1-L99

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

theorem Problem97.CGN.edgeAt_mem_powersetCard {m : ℕ} {A : Finset ℝ²} (L : OrderedCap m)
    (hmem : ∀ t : Fin m, L.points t ∈ A) {r s : Fin m} (hrs : r < s) :
    edgeAt L r s ∈ A.powersetCard 2 := by sorry
