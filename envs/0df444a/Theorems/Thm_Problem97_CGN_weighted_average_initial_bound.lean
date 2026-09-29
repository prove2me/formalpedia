-- Prove2me | Theorems.Thm_Problem97_CGN_weighted_average_initial_bound
-- name    : Problem97.CGN.weighted_average_initial_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:46:25.54667+00:00
-- url     : https://prove2.me/theorems/e775f6ca-761e-4d6d-9397-813fd27fcbd1
-- title:
--   Initial Weighted Average Bound for a Decreasing Sequence
-- statement:
--   Let d be weakly decreasing on the integer interval [a,b), and let every weight w(t) on that interval be strictly positive. For a < i < b, the weighted average of d over the prefix [a,i) is at least its weighted average over all of [a,b).
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_weighted_average_initial_bound.lean#L1-L144

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN6 by Stage 2 proof cut; source SHA-256 87eeea2860c10b6c484c3d7aec9f295605a553c9956e5cc04bbc649402bc9c30 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Order.Interval.Finset.Fin
open Problem97 Problem97.CGN



/-!
# CGN6: normalized minor-cap chain model

This file starts the CGN6 layer named in the updated counterexample-card-ge-nine
prose. It records the normalized minor-cap chain data the prose uses for the
CGN6b slope-product argument: ordered coordinates, endpoint normalization, the
unit-disk bound, and the adjacent-slope bookkeeping.

The actual geometric construction of this model from a concrete MEC cap packet
is still separate. This file only provides the data interface the subsequent
CGN6b / CGN6c proofs will consume.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators


























/- ### CGN6norm scaffold

The prose normalization theorem uses an explicit coordinate frame
centered at the chord midpoint and aligned with the chord / inward
normal directions.  The full packet-to-frame bridge is still separate;
this helper records the coordinate map in the exact algebraic form used
by the prose.
-/































-- The normalization proof is large enough to need a higher elaboration budget.

theorem Problem97.CGN.weighted_average_initial_bound
    {w d : ℕ → ℝ} {a i b : ℕ}
    (hai : a < i) (hib : i < b)
    (hmono : ∀ {t u : ℕ}, a ≤ t → t < u → u < b → d t ≥ d u)
    (hwpos : ∀ t ∈ Finset.Ico a b, 0 < w t) :
    (∑ t ∈ Finset.Ico a i, w t * d t) / (∑ t ∈ Finset.Ico a i, w t) ≥
      (∑ t ∈ Finset.Ico a b, w t * d t) / (∑ t ∈ Finset.Ico a b, w t) := by sorry
