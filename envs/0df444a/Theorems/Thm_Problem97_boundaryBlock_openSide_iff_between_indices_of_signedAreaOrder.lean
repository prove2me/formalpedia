-- Prove2me | Theorems.Thm_Problem97_boundaryBlock_openSide_iff_between_indices_of_signedAreaOrder
-- name    : Problem97.boundaryBlock_openSide_iff_between_indices_of_signedAreaOrder
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:44:19.25979+00:00
-- url     : https://prove2.me/theorems/bad3356e-9633-4035-a668-d1df44657a8e
-- title:
--   The Open Side of a Subchord Selects the Intermediate Vertices
-- statement:
--   Let L be a boundary block in a signed-area-ordered enumeration of A, with no three distinct points of A collinear. For local indices r < s and any x in A, x lies on the positive open side of the chord from L(r) to L(s) precisely when x is L(j) for some local index j strictly between r and s.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_boundaryBlock_openSide_iff_between_indices_of_signedAreaOrder.lean#L1-L120

/- Generated theorem stub from Erdos9796Proof.P97.CGN.CGN4g by Stage 2 proof cut; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
open Problem97



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

theorem Problem97.boundaryBlock_openSide_iff_between_indices_of_signedAreaOrder
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : Problem97.CGN.OrderedCap m}
    (Block : Problem97.CGN.BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (_hno3 : ∀ {x y z : ℝ²}, x ∈ A → y ∈ A → z ∈ A →
      x ≠ y → y ≠ z → x ≠ z →
      Problem97.signedArea2 x y z ≠ 0) :
    ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
      (0 < Problem97.signedArea2 (L.points r) (L.points s) x ↔
        ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x) := by sorry
