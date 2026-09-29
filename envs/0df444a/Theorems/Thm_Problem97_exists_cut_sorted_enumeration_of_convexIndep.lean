-- Prove2me | Theorems.Thm_Problem97_exists_cut_sorted_enumeration_of_convexIndep
-- name    : Problem97.exists_cut_sorted_enumeration_of_convexIndep
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:11:53.508079+00:00
-- url     : https://prove2.me/theorems/3b4d5e00-b877-49c9-adfd-e8ae9e791bfe
-- title:
--   Construct a Cut-Sorted Enumeration
-- statement:
--   If c is an interior point of the convex hull of a convex-independent finite set A, then A has an injective enumeration φ by Fin A.card whose image is A and whose cut keys of the angular values around c are strictly increasing.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_exists_cut_sorted_enumeration_of_convexIndep.lean#L1-L218

/- Generated theorem stub from Erdos9796Proof.P97.ConvexCyclicOrder.Construct by Stage 2 proof cut; source SHA-256 57dc74b4cc61e00d4333c450728c8f4df96124ae963c47fc084dbfa1f368bf19 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_ConvexCyclicOrder_Construct
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_ArcAngle
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Finset.Sort
open Problem97




/-!
# ConvexCyclicOrder Step 2 — polar-sort construction (partial)

Constructive content toward `Problem97.exists_isCcwConvexPolygon_of_convexIndep`
(Step 2 of the ConvexCyclicOrder construction lane used by the CGN bridge).

Strategy (locked in `docs/97-convex-cyclic-order-step2-spec.md`): enumerate `A`
by angular order around an interior point `c` of `convexHull A`, using the
in-tree `Problem97.arcAngle c · : ℝ² → Real.Angle` and Mathlib's
`Real.Angle.instCircularOrder`, cutting the circular order open at an anchor.

This file currently lands the independent sub-lemmas and the geometric
injectivity sub-lemma:

* `exists_center_interior_convexHull_of_convexIndep_noncoll` (spec §3.1) — an
  interior point of `convexHull A` exists, from `¬ Collinear ⇒ affineSpan = ⊤`.
* `three_le_card_of_convexIndep_noncoll` (spec §3.6) — `¬ Collinear ⇒ 3 ≤ A.card`.
* `arcAngle_injective_of_center_interior` (spec §3.2) — for an interior center
  `c`, `arcAngle c ·` is injective on a convex-independent `A`. Distinct points
  on a common ray from `c` would force the nearer one to be an interior point of
  the hull, contradicting convex independence.

Supporting lemmas proved en route to §3.2:

* `notMem_extremePoints_of_mem_interior` — an interior point of any set in `ℝ²`
  is never an extreme point (midpoint-of-a-ball argument).
* `notMem_convexHull_diff_convexHull_of_notMem` — a Carathéodory/Hahn-Banach
  "descent": `a ∉ convexHull (A \ {a}) ⇒ a ∉ convexHull (convexHull A \ {a})`.
* `mem_extremePoints_of_convexIndep` — convex-independent points are extreme
  points of the hull.
* `notMem_interior_of_convexIndep` — convex-independent points are not interior
  to the hull.

It also lands the cut-open enumeration:

* `cutKey` (spec §3.3) — the cut-open linear key on `Real.Angle`, taken as
  `-Real.Angle.toReal` (anchor at `0`, i.e. the `+x` direction). It is globally
  injective because `toReal` is, which is all the *enumeration* lemma needs. The
  key is **negated** so that increasing `cutKey ∘ arcAngle c` walks the boundary
  *clockwise* in the standard orientation: a direct integer-coordinate check
  (recorded in `cutKey`'s docstring) shows this is the chirality
  `IsCcwConvexPolygon` requires (`(∡ ·)·.sign = 1`), whereas the
  counter-clockwise walk gives sign `-1`. This makes the enumeration directly
  consumable by the §3.5 geometric heart.
* `exists_cut_sorted_enumeration_of_convexIndep` (spec §3.4) — sort `A` by the
  cut-open key into `φ : Fin A.card → ℝ²`, strictly monotone in the key. Pure
  bookkeeping over `Finset.orderEmbOfFin` of the key-image, using §3.2 for
  injectivity of the key on `A`.

The remaining sub-lemma — §3.5, the geometric heart (cyclic angular order ⇒
CCW), and the final assembly — are **not** in this file yet; see
`docs/97-convex-cyclic-order-step2-spec.md` §3.5 and the risk register.
-/

open scoped EuclideanGeometry Real



/-! ### §3.6 — cardinality lower bound -/



/-! ### §3.1 — interior point of the convex hull -/





/-! ### Supporting helper — interior points are not extreme

An interior point of any set in `ℝ²` cannot be an extreme point: it is the
midpoint of two distinct nearby points of the set (obtained from a ball inside
the interior), so it is a non-trivial convex combination, contradicting the
extreme-point definition. -/



/-! ### §3.2 — `arcAngle` injective on `A` for an interior center

If `c` is interior to `convexHull A`, two distinct convex-independent points of
`A` cannot share a ray from `c`: the nearer one would be a strictly interior
point of the hull, contradicting convex independence. We package this through a
sequence of standard convexity facts: a Hahn-Banach "descent" lemma, the
extreme-point characterization of the hull, and the interior/extreme
incompatibility above. The injectivity statement lives on `Real.Angle` (not
`.toReal`), as required by the cut-open enumeration in §3.4. -/













/-! ### §3.3 / §3.4 — cut-open linear key and the sorted enumeration -/

theorem Problem97.exists_cut_sorted_enumeration_of_convexIndep
    {A : Finset ℝ²} {c : ℝ²}
    (hA : Problem97.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²))) :
    ∃ φ : Fin A.card → ℝ²,
      Function.Injective φ ∧
      Finset.univ.image φ = A ∧
      StrictMono (fun i => cutKey (Problem97.arcAngle c (φ i))) := by sorry
