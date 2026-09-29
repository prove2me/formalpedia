-- Prove2me | Theorems.Thm_Problem97_card_ge_five_of_K4
-- name    : Problem97.card_ge_five_of_K4
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:56:38.664391+00:00
-- url     : https://prove2.me/theorems/d3df4af2-5c9b-4779-8237-55b72a7ae55b
-- title:
--   Four equidistant neighbours require at least five vertices
-- statement:
--   Let $A$ be a nonempty finite set of points in the Euclidean plane. Suppose that every point $p\in A$ has at least four points of $A$ at one common positive distance from $p$, with the radius allowed to depend on $p$. Then $|A|\ge 5$. This is the first cardinality bound in the counting obstruction.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_card_ge_five_of_K4.lean#L1-L38

/- Generated theorem stub from Erdos9796Proof.P97.Counting by Stage 2 proof cut; source SHA-256 1bc8e15663c147d582d82d71a22bf654f8becdb1003f0aef828d47271d204523 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
open Problem97



/-!
# Counting obstruction: `9 ≤ |A|` (Milestone 3)

This module packages the proven lower bound
`Problem97.six_mul_card_le_iCount_of_K4` and the proven arithmetic core
`Problem97.counting_arithmetic` into the intermediate theorem
`Problem97.counterexample_card_ge_nine_of_iCount_upper_bound`.

The top-level theorem `Problem97.counterexample_card_ge_nine` now
instantiates that reducer with the circumscribed-branch CGN closure
`Problem97.CGN8_circumscribed_iCount_upper_bound`.
-/

open scoped EuclideanGeometry
open Finset

theorem Problem97.card_ge_five_of_K4 {A : Finset ℝ²} (hne : A.Nonempty)
    (hK4 : HasNEquidistantProperty 4 A) : 5 ≤ A.card := by sorry
