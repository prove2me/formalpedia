-- Prove2me | Theorems.Thm_Problem97_MEC_no_diameter_under_k4
-- name    : Problem97.MEC.no_diameter_under_k4
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:10:11.03472+00:00
-- url     : https://prove2.me/theorems/211a267a-bf56-402d-bc74-7004df294cab
-- title:
--   No MEC Diameter Under the 4-Equidistant Property
-- statement:
--   For a nonempty noncollinear convex-independent finite planar set with the 4-equidistant property, at least three points lie on the boundary of its minimum enclosing circle.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_MEC_no_diameter_under_k4.lean#L1-L121

/- Generated theorem stub from Erdos9796Proof.P97.NoDiameterUnderK4 by Stage 2 proof cut; source SHA-256 6ce8b4da44107edce310a178f612914b094548c6bcfd7d92ba484e7e4b2fb159 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
open Problem97 Problem97.MEC



/-!
# MEC has at least 3 boundary vertices under `K4` (Lemma 2)

For a nonempty noncollinear convex-independent `A : Finset ℝ²` with the
4-equidistant property, the MEC of `A` cannot land in the Sylvester
*diameter* case: at least three points of `A` must lie on the MEC
boundary.

This is **Lemma 2** of the Erdős Problem 97 general proof (see the
closure plan in `docs/`).

## Argument (Option C — direct convex-hull contradiction)

Suppose for contradiction the diameter case holds: there exist `a, b ∈ A`
on the MEC boundary, with `MEC.center = midpoint a b` and
`MEC.radius = dist a b / 2`.

By the 4-equidistant hypothesis at apex `a ∈ A`, pick `r > 0` such that
`S := A.filter (dist a · = r)` has card ≥ 4.

**Geometric core.**  Each `q ∈ S` lies in the closed MEC disk, which has
`ab` as diameter.  Thales' theorem rephrases this as
`⟨q - a, q - b⟩ ≤ 0`, equivalently `⟨q - a, b - a⟩ ≥ ‖q - a‖² = r²`.

Define `x_q := ⟨q - a, b - a⟩` and `y_q := cross(b - a, q - a)` where
`cross(u, v) := u 0 * v 1 - u 1 * v 0`.  The 2D Lagrange identity gives
`x_q² + y_q² = d² · r²` (so `r ≤ d`, since `x_q² ≥ r⁴`).

For `q ∈ S \ {b}`, we'll show `y_q ≠ 0` (the point is strictly off line
`ab`), so by pigeonhole two of the four equidistant points have same
sign of `y_q`.  Then a convex-combination computation shows the smaller
one is in the convex hull of `{a, larger one, b}`, contradicting
`ConvexIndep A`.

## Main theorem

`Problem97.MEC.no_diameter_under_k4` — the MEC boundary has card ≥ 3,
ruling out the diameter case under K4 + ConvexIndep.
-/

open scoped EuclideanGeometry
open Finset




/- ### Coordinate helpers -/













/- ### Thales / midpoint identities -/





/- ### Auxiliary: points in disk on line `ab` are in segment `[a, b]`. -/



/- ### Pair-in-half-plane contradiction.

The technical heart: given `0 < y₁ < y₂`, `x_i² + y_i² = r²`,
`x_i d ≥ r²` (i.e. `q_i` in closed disk diameter `[a, b]` projected),
and `d ≥ r > 0`, the point `q₁ = (x₁, y₁) + a` lies in the convex hull
of `{a, q₂ + a + …, b}` where `q_2 = (x₂, y₂)`.

Concretely we prove `q₁ ∈ convexHull ℝ {a, q₂, b}` via the explicit
convex combination weights `α, β, γ`. -/





/- ### Helper: ordered-pair contradiction (the inner core).

This is the core of the same-sign argument: assuming `|y_a| < |y_b|`,
construct the convex combination expressing `q_a` as `α • a + β • q_b + γ • b`
with all weights positive, then apply `ConvexIndep A`. -/


/- ### Helper: same-sign-pair contradiction.

Given two distinct points `q1, q2 ∈ A` both on circle `(a, r)`, strictly
inside the disk on diameter `[a, b]`, and lying on the *same side* of
line `ab` (positive product of cross products), we derive a contradiction
with `ConvexIndep A`: by Lagrange and `key_trig_inequality`, the point
with smaller `|cross|` lies in `convexHull {a, b, q (other)}`. -/


/- ### The main proof: derive contradiction from the diameter case. -/

theorem Problem97.MEC.no_diameter_under_k4
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²))
    (hConv : Problem97.ConvexIndep A)
    (hK4 : Problem97.HasNEquidistantProperty 4 A) :
    3 ≤ (A.filter (fun p => dist p (Problem97.MEC.mec A hA).center
                            = (Problem97.MEC.mec A hA).radius)).card := by sorry
