-- Prove2me | Theorems.Thm_Problem97_MEC_sylvester_dichotomy
-- name    : Problem97.MEC.sylvester_dichotomy
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:59:23.48383+00:00
-- url     : https://prove2.me/theorems/fd5ee090-f7d4-4041-8e0e-beccc75bbbbd
-- title:
--   Minimum-enclosing-circle support dichotomy
-- statement:
--   Let $A$ be a nonempty, noncollinear finite set in the Euclidean plane, and let its minimum enclosing circle have center $O$ and radius $R$. Either two distinct boundary points $p,q\in A$ form a diameter, so $O$ is their midpoint and $R=d(p,q)/2$, or at least three points of $A$ lie on the circle. This supplies the diameter-versus-circumscribed branch split for the counting proof.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_MEC_sylvester_dichotomy.lean#L1-L134

/- Generated theorem stub from Erdos9796Proof.P97.MEC.Boundary by Stage 2 proof cut; source SHA-256 e7d16b0637be4dd967cade4cfb9db7d4ba52c8fdb229ece7b87498ff207e21a7 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
open Problem97 Problem97.MEC



/-!
# MEC boundary structure — Sylvester (1857) dichotomy

For any nonempty noncollinear finite point set `A ⊆ ℝ²` we prove the
classical Sylvester dichotomy on the minimum enclosing circle (MEC) of
`A`:

* **Diameter case** — two points of `A` lie diametrically opposite on
  the MEC boundary, pinning the centre to their midpoint, OR
* **Circumscribed case** — at least three points of `A` lie on the MEC
  boundary.

The naive "≥3 boundary points" statement is **false** in general:
obtuse triangles realise the diameter case (the two acute-angle vertices
form an antipodal pair on the MEC, the obtuse vertex sits strictly
inside).  The disjunction below is the correct formulation, due to
Sylvester (1857).

The argument is variational.  Define
`B(A) := { p ∈ A | dist p M.center = M.radius }`, the set of points
realising the maximum distance from the MEC centre.  Then:

* `B.card = 0` is impossible: by continuity of `radF`, every point sits
  strictly inside, so we can shrink `M.radius` keeping the centre fixed
  — contradicting minimality.
* `B.card = 1` is impossible for noncollinear `A`: perturb the centre
  toward the lone boundary point.  Strict interior distance to other
  points is preserved by continuity, so we obtain a smaller enclosing
  radius — contradicting minimality.
* `B.card = 2` forces the diameter case: the two boundary points
  `p, q` pin the centre to their midpoint (otherwise we could shift
  along the perpendicular bisector toward `midpoint p q` to shrink the
  radius — same contradiction).
* `B.card ≥ 3` is the circumscribed case by definition.

The core perturbation uses an algebraic identity: along the segment
from `c := M.center` toward a target `q*` chosen so that
`⟨p - c, q* - c⟩ = ‖q* - c‖²` for every boundary point `p ∈ B`,
the squared distance `‖p - c'(t)‖²` equals
`M.radius² + (t² - 2t) ‖q* - c‖²`, which is strictly less than
`M.radius²` for `t ∈ (0, 2)` (and `q* ≠ c`).  For interior points the
distance change is bounded by `t · ‖q* - c‖`, so picking `t` small
enough keeps them inside as well.

## Main theorem

* `Problem97.MEC.sylvester_dichotomy` — the Sylvester (1857) dichotomy
  in disjunctive form, suitable for downstream consumers branching on
  the two cases.
-/

open scoped EuclideanGeometry
open Finset




/- ### Boundary set of the MEC -/







/- ### Auxiliary helpers -/









/- ### Boundary card lower bound: ≥ 1 -/



/- ### Sentinel computation: distance along a "shrink-toward-target" line.

We isolate the algebraic identity that underlies both the card-1 and card-2
variational arguments.  If `p, c, q* : ℝ²` satisfy
`⟨p - c, q* - c⟩ = ‖q* - c‖²`, then
`‖p - (c + t • (q* - c))‖² = ‖p - c‖² - (2t - t²) ‖q* - c‖²`.

For `card = 1` with single boundary point `p₀`, take `q* := p₀`; then
`⟨p₀ - c, p₀ - c⟩ = ‖p₀ - c‖² = M.radius² = ‖q* - c‖²` (uses `q* - c = p₀ - c`).

For `card = 2` with boundary `{p, q}`, take `q* := midpoint p q = m`; then
on the perpendicular bisector, `⟨p - c, m - c⟩ = ‖m - c‖²`.
-/





/- ### Card 1 case — impossible for noncollinear A -/



/- ### Card 2 case — diameter case -/









/- ### Main theorem -/

theorem Problem97.MEC.sylvester_dichotomy
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²)) :
    (∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧
        dist p (mec A hA).center = (mec A hA).radius ∧
        dist q (mec A hA).center = (mec A hA).radius ∧
        (mec A hA).center = midpoint ℝ p q ∧
        (mec A hA).radius = dist p q / 2)
      ∨ 3 ≤ (A.filter (fun p => dist p (mec A hA).center = (mec A hA).radius)).card := by sorry
