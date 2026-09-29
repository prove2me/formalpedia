-- Prove2me | Theorems.Thm_Problem97_iCountAt_ge_six_of_K4
-- name    : Problem97.iCountAt_ge_six_of_K4
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:58:55.091161+00:00
-- url     : https://prove2.me/theorems/53f8c281-0d9e-48f7-9fff-d8a43890f17e
-- title:
--   Four equidistant neighbours yield six isosceles base pairs
-- statement:
--   Let $A$ be a finite planar point set and $p$ a point. If at least four members of $A$ lie at one common positive distance from $p$, then at least six unordered two-point subsets of $A\setminus\{p\}$ are equidistant from $p$. In the notation of the formalization, the local isosceles count satisfies $i_A(p)\ge {4\choose 2}=6$.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_iCountAt_ge_six_of_K4.lean#L1-L64

/- Generated theorem stub from Erdos9796Proof.P97.IsoscelesCount by Stage 2 proof cut; source SHA-256 207564b11a38e9270192c8e5de3202b113b7f89c7ece5af3bc12954928d3013c -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
open Problem97



/-!
# Isosceles count for Erdős Problem 97 (Dumitrescu lower bound, Milestone 3)

Defines the per-vertex and total isosceles count of a finite point set,
in the Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013 convention
(equilaterals counted three times), and proves the easy lower bound:

  Per-vertex `K4` ⇒ each vertex contributes `≥ C(4,2) = 6` isosceles pairs.
  Summing: `6 · |A| ≤ I(A)`.

The matching upper bound `I(A) ≤ (11·|A|²−18·|A|)/12` for convex point
sets is Dumitrescu 2006 eq. (5), still open
(`p97-isosceles-count-upper-bound`).

References: doc slug `p97-isosceles-obstruction`.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

theorem Problem97.iCountAt_ge_six_of_K4 (A : Finset ℝ²) (p : ℝ²)
    (hp : HasNEquidistantPointsAt 4 A p) : 6 ≤ iCountAt A p := by sorry
