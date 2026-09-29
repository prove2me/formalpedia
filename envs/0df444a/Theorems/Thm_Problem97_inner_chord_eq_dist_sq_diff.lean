-- Prove2me | Theorems.Thm_Problem97_inner_chord_eq_dist_sq_diff
-- name    : Problem97.inner_chord_eq_dist_sq_diff
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:57:55.216199+00:00
-- url     : https://prove2.me/theorems/f11a366a-5331-406b-9ad3-2f67b143ca57
-- title:
--   Chord-side polarization identity
-- statement:
--   For points $a,c,y$ in the Euclidean plane, with $m$ the midpoint of $a$ and $c$, $$2\langle y-m, c-a\rangle=d(y,a)^2-d(y,c)^2.$$ The identity converts a half-plane test relative to the perpendicular bisector of $ac$ into a comparison of the two distances, and is used in the cap-witness geometry.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_inner_chord_eq_dist_sq_diff.lean#L1-L257

/- Generated theorem stub from Erdos9796Proof.P97.Dumitrescu.Lc1Strict by Stage 2 proof cut; source SHA-256 79552d47d9473f42104d5850f982510576893e85ddd7347652348a1f8b91502b -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Triangle
open Problem97




/-!
# Perpendicular-bisector half-plane comparison

This file deposits the **load-bearing chord-side / half-plane lemma**
used by Nivasch–Pach–Pinchasi–Zerbib 2013 Lemma 6 (the witness-monotonicity argument that
underlies both Dumitrescu L5 `CapWitnessRanking` and Dumitrescu Lc3
`CapDiagonalVertexProfile`).

## Paper provenance

Nivasch–Pach–Pinchasi–Zerbib 2013 (arXiv:1207.1266) §2 Lemma 6 begins its proof with:

> "We have `|yc| ≥ |ya| = |yb|`."

The "`|yc| ≥ |ya|`" half of this chain is **not** a consequence of
strict-monotone-distance along a cap arc (which would require all cap
points to lie on the MEC sphere — they don't, in our setup). It is a
**linear-algebra** fact about which side of the perpendicular bisector
of `ac` the point `y` sits on:

* `x` witnesses edge `ac` ⟹ `x` lies on the perpendicular bisector of
  `ac` (`dist x a = dist x c`).
* `y` "between `a` and `x` in convex order" ⟹ `y` lies on the closed
  half-plane on `a`'s side of the perpendicular bisector of `ac` (this
  is the convex-position consequence — *open* and not in scope here).
* Once `y` is on `a`'s side of the perpendicular bisector, the
  comparison `|ya| ≤ |yc|` is immediate from the polarisation identity.

This file proves the **third bullet** in isolation as a clean Mathlib-
style inner-product lemma. The second bullet (convex order ⟹ half-plane
side) is the **genuinely missing piece** of the Lemma 6 proof in our
setting and is **not** discharged here — see the "What's NOT in this
file" section below for the precise statement of the open obligation.

## What IS in this file (provable today)

### `inner_chord_eq_dist_sq_diff` (polarisation identity)

For any three points `a, c, y : ℝ²`:
```
2 * ⟪y - midpoint a c, c - a⟫_ℝ = dist y a ^ 2 - dist y c ^ 2.
```

This is the central algebraic identity. Pure inner-product algebra;
no geometry. The signed quantity on the left is the **chord-side
test** ("which side of the perpendicular bisector of `ac` does `y` lie
on?") and the right-hand side is the **distance-comparison test**.

### `dist_le_iff_inner_chord_nonpos`

Direct equivalence: `dist y a ≤ dist y c ↔ ⟪y - m, c - a⟫_ℝ ≤ 0`,
where `m = midpoint a c`. This is what Lemma 6's chain
"`|yc| ≥ |ya|`" needs as its *input*.

### `dist_lt_iff_inner_chord_neg`

Strict variant: `dist y a < dist y c ↔ ⟪y - m, c - a⟫_ℝ < 0`.

### `dist_le_of_inner_chord_le_zero`

The "easy direction" packaged as a stand-alone implication: the
algebraic chord-side condition implies the distance comparison.

### `same_side_perpBisector_dist_le`

Cap-witness flavored re-statement: if `x` witnesses edge `(a, c)`
(`dist x a = dist x c`) and `y` lies on `a`'s closed half-plane of the
perpendicular bisector of `ac` (`⟪y - x, c - a⟫_ℝ ≤ 0`), then
`dist y a ≤ dist y c`.

## What is NOT in this file (Lemma 6's gap)

Nivasch–Pach–Pinchasi–Zerbib Lemma 6's actual proof requires three more ingredients that
are **all open** in the current infrastructure:

### Gap 1 — `convex_order_implies_perpBisector_side`  (NOT proven)

For four points `a, y, x, c` in `ℝ²` in **convex position**, with
convex polygon order `a, y, x, ..., c, ...` (i.e. `y` strictly between
`a` and `x` in the polygon ordering, and `x` strictly between `a` and
`c`), and `x` on the perpendicular bisector of `ac`, then `y` lies on
`a`'s side of that perpendicular bisector:

```text
⟪y - midpoint a c, c - a⟫_ℝ ≤ 0.
```

This is the "second bullet" of the Lemma 6 chain. **It requires a
convex-position angular monotonicity argument** that is not in current
infrastructure: as `y` moves along the convex polygon from `a` towards
`x`, the chord-side projection on the perp bisector of `ac` is
monotone. The argument uses general-position convexity, not just the
chord-side / disk-containment data we currently package.

### Gap 2 — wedge containment (`∠acb ≤ ∠ycb`)  (NOT proven)

Nivasch–Pach–Pinchasi–Zerbib Lemma 6 then derives a contradiction by combining
`∠acb ≥ π/2` (cap-Thales at the cap-endpoint chord) with
`∠ycb ≤ π/2` (chord-side argument inside △ycb using `|yc| ≥ |yb|`)
**and** the wedge containment `∠acb ≤ ∠ycb`. The last piece — that the
angle subtended at `c` by `ab` is at most the angle subtended by `yb`
— is another convex-position monotonicity statement, similarly not in
current infrastructure.

### Gap 3 — cap-Thales-at-all-triples generalization  (NOT proven)

Definition 3 of Nivasch–Pach–Pinchasi–Zerbib 2013 (p. 4) gives a cap-Thales iff at the
*cap endpoints*. Our `inner_nonpos_of_cap_region_thales` discharges
this in `lc1_capArcThales_C{1,2,3}` for cap-points subtending the
*Moser-vertex chord* — exactly the cap-endpoint case. The diagonal-
vertex argument (Dumitrescu §2 p. 3-4 / Nivasch–Pach–Pinchasi–Zerbib Corollary 7 proof)
**does not require the all-triples generalization** — it composes
Lemma 6 (applied with various choices of cap endpoints) with the
positional constraint. So Gap 3 is *not* on the Lemma 6 critical
path, but is flagged here for completeness.

## Composition status

This file by itself **does not close** either L5 `CapWitnessRanking`
constructor or Lc3 strong-form `CapDiagonalVertexProfile`. Closing
Lemma 6 — and through it both downstream targets — requires Gap 1 +
Gap 2 above, which are **out of scope for this dispatch** by the
brief's "if genuinely unprovable from current infrastructure, surface
the gap" guidance.

The half-plane comparison lemma here is a clean, axiom-clean,
self-contained Mathlib-style deposit. When the convex-order /
perpendicular-bisector half-plane bridge is later landed (Gap 1),
together with the wedge containment (Gap 2), Lemma 6 will compose
without further analytic work.

## References

* Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, *The Number of Distinct Distances from a Vertex of a Convex Polygon*, Journal of Computational Geometry 4 (2013), 1–12; arXiv:1207.1266 (2012 preprint).
* Adrian Dumitrescu (2006), *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Computational Geometry 36, 503–509. DOI: 10.1007/s00454-006-1262-y. Lemma 2, Corollary 1 (p. 3-4).
-/

open scoped EuclideanGeometry InnerProductSpace
open Finset



/- ### Polarisation identity for the perpendicular-bisector half-plane test

The central algebraic fact: the signed "chord-side test"
`⟪y - midpoint a c, c - a⟫_ℝ` and the squared-distance comparison
`dist y a ^ 2 - dist y c ^ 2` are related by a factor of 2. From this
one identity all four "perpendicular bisector half-plane vs distance
comparison" lemmas in this file follow by basic real algebra.

The identity expands `dist y a ^ 2 - dist y c ^ 2` via
`norm_sub_sq_real`:
```
dist y a ^ 2 = ‖y - a‖^2 = ‖y‖^2 - 2 ⟪y, a⟫ + ‖a‖^2,
dist y c ^ 2 = ‖y - c‖^2 = ‖y‖^2 - 2 ⟪y, c⟫ + ‖c‖^2.
```
Subtracting and rearranging:
```
dist y a ^ 2 - dist y c ^ 2
  = 2 ⟪y, c - a⟫ + (‖a‖^2 - ‖c‖^2)
  = 2 ⟪y, c - a⟫ - ⟪a + c, c - a⟫
  = ⟪2 y - (a + c), c - a⟫
  = 2 ⟪y - midpoint a c, c - a⟫,
```
since `midpoint a c = (a + c) / 2`, hence `2 · midpoint a c = a + c`.

This gives the stated form. -/

theorem Problem97.inner_chord_eq_dist_sq_diff (a c y : ℝ²) :
    2 * ⟪y - midpoint ℝ a c, c - a⟫_ℝ
      = dist y a ^ 2 - dist y c ^ 2 := by sorry
