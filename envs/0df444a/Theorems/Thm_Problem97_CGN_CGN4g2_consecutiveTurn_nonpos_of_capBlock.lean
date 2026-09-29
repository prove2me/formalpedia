-- Prove2me | Theorems.Thm_Problem97_CGN_CGN4g2_consecutiveTurn_nonpos_of_capBlock
-- name    : Problem97.CGN.CGN4g2_consecutiveTurn_nonpos_of_capBlock
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:43:14.987713+00:00
-- url     : https://prove2.me/theorems/38a4cd7e-920c-4fed-88fe-c38215253aee
-- title:
--   Consecutive Turns in a Boundary Cap Are Nonpositive
-- statement:
--   Suppose an ordered cap L is embedded as a boundary block in an enumeration φ, and every increasing triple of indices in φ has strictly negative signed area. Then every three consecutive vertices of L have nonpositive signed area.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_CGN_CGN4g2_consecutiveTurn_nonpos_of_capBlock.lean#L1-L125

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN4g by Stage 2 proof cut; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
open Problem97 Problem97.CGN



/-!
# CGN4g: ordered-cap block packaging

This file adds the closure-plan data carrier for the ordered-cap block cut out
of a global convex-boundary enumeration, together with the theorem wrappers
that are pure packaging.

The geometric producers for the block (`CGN4g1`, `CGN4g3`, `CGN4g4`) remain
separate. The declarations here are the sanctioned interfaces consumed by the
existing CGN6 / CGN7 layers.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace












variable {A C : Finset ℝ²}

theorem Problem97.CGN.CGN4g2_consecutiveTurn_nonpos_of_capBlock
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : OrderedCap m}
    (Block : BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0) :
    ∀ t : ℕ, ∀ ht : t + 2 < m,
      Problem97.signedArea2
        (L.points ⟨t, by
          exact lt_trans
            (Nat.lt_add_of_pos_right (by decide : 0 < (2 : ℕ))) ht⟩)
        (L.points ⟨t + 1, by
          exact lt_trans
            (Nat.succ_lt_succ (Nat.lt_add_of_pos_right (by decide : 0 < (1 : ℕ))))
            ht⟩)
        (L.points ⟨t + 2, by
          exact ht⟩) ≤ 0 := by sorry
