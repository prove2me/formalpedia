-- Prove2me | Theorems.Thm_Problem97_cap_sum_identity
-- name    : Problem97.cap_sum_identity
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:50:20.420752+00:00
-- url     : https://prove2.me/theorems/f6649239-f223-40d5-bef6-e34336a12183
-- title:
--   Three-Cap Cardinality Sum Identity
-- statement:
--   For a cap partition of a finite set S determined by a three-element Moser subset, the cardinalities of the three closed caps sum to |S| + 3: each Moser vertex belongs to two caps, while every other vertex belongs to exactly one.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_cap_sum_identity.lean#L1-L60

/- Generated theorem stub from Erdos9796Proof.P97.Cap.Partition by Stage 2 proof cut; source SHA-256 baaf503023695b8e0b1c19f8745478e6ec02a514e175bd113f5346c7d25a5e27 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Cap_Partition
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff
open Problem97



/-!
# Cap-partition sum identity (Erdős Problem 97, Milestone 4)

Pure combinatorics extracted from the geometric setup in the universal
proof of Erdős Problem 97 (`p97-positive-defect-bridge`).

**Geometric origin.** In the universal-descent argument for Problem 97
(see `docs/97-uniform-theorem-closure-plan.md`), a convex counterexample
`P` to the 4-equidistant property carries three "caps" `C₁, C₂, C₃` cut
out by closed chains between three selected Moser vertices.  Each Moser vertex lies on exactly two opposite caps and
every other vertex on exactly one of the three chains, so

  `|C₁| + |C₂| + |C₃| = n + 3`

where `n = |P|`.

The geometry only enters via the membership pattern.  Once you fix it,
the identity is a pure counting lemma:

* a finset `S` (the vertex set),
* a 3-element subset `M ⊆ S` (the Moser vertices),
* three subsets `C₁, C₂, C₃ ⊆ S` such that every Moser vertex hits
  exactly two of them and every non-Moser vertex hits exactly one,

then `|C₁| + |C₂| + |C₃| = |S| + 3`.

Both pieces of data ("Moser vertex ⇒ in exactly two caps" and
"non-Moser ⇒ in exactly one cap") are packaged in a structure
`CapPartition` so the geometric obligation can hand the combinatorics
a single bundled object.

This is `p97-cap-sum-identity` (Milestone 4 sub-step 2 of 4).  It is
independent of the geometric existence proofs and provable from the
structural setup alone.
-/

open Finset

theorem Problem97.cap_sum_identity {α : Type*} [DecidableEq α]
    {S M : Finset α} (cp : CapPartition S M) :
    cp.C1.card + cp.C2.card + cp.C3.card = S.card + 3 := by sorry
