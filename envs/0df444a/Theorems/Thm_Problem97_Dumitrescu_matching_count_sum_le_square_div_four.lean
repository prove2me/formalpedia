-- Prove2me | Theorems.Thm_Problem97_Dumitrescu_matching_count_sum_le_square_div_four
-- name    : Problem97.Dumitrescu.matching_count_sum_le_square_div_four
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:58:24.708311+00:00
-- url     : https://prove2.me/theorems/0d093f51-aa0f-423e-b18e-e87432337838
-- title:
--   The cap matching profile is bounded by one quarter of a square
-- statement:
--   For every natural number $m$, $$\sum_{j=0}^{m-1}\min\{j,m-1-j\}\le \left\lfloor\frac{(m-1)^2}{4}\right\rfloor.$$ This parity computation is the numerical core of the per-cap witness bound: a vertex at position $j$ can match only vertices on opposite sides of its place in the cap order.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_Dumitrescu_matching_count_sum_le_square_div_four.lean#L1-L178

/- Generated theorem stub from Erdos9796Proof.P97.Dumitrescu.Lc3 by Stage 2 proof cut; source SHA-256 b2da9a0610fa56db34d79cd9a30e8c812ed7feff3d0f6345aea81fb7298fe167 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
open Problem97 Problem97.Dumitrescu



/-!
# Dumitrescu Lc3 — in-cap isosceles bound (Corollary 1)

This file packages the **in-cap isosceles bound** that Dumitrescu 2006
Corollary 1 / Lemma 2 supplies in the Sylvester-circumscribed branch.
The target inequality is

  `∑_{a ∈ Cᵢ} |IsoscelesPairsAt(Cᵢ, a)| ≤ (mᵢ − 1)² / 4`     (Lc3)

where `mᵢ = Cᵢ.card`. In ℕ-arithmetic this is rephrased as the
`4 ·`-form

  `4 · ∑_{a ∈ Cᵢ} |IsoscelesPairsAt(Cᵢ, a)| ≤ (mᵢ − 1)²`,

which avoids the integer-division floor.

## Why two bounds, and what's blocked

The Dumitrescu Cor 1 proof is the **diagonal-vertex argument** on a
cap's MEC arc: under the *strict-monotone-distance* form of Lc1, the
iso-pairs at each apex `a ∈ Cᵢ` split into pairs with one endpoint on
each side of `a` in the cap-arc order, capping the per-apex count by
`min(j − 1, mᵢ − j)` where `j` is `a`'s 1-indexed arc-position. The
∑ over `j = 1..mᵢ` is exactly `⌊(mᵢ − 1)² / 4⌋`.

The current Lc1 infrastructure (commit ee017cd) carries only the
**Thales-form** of Lc1 — every cap-point sees the cap's opposing
Moser-vertex chord at angle ≥ π/2 — which is **not sufficient** for
the diagonal-vertex argument. Closing the strict-monotone-distance Lc1
requires either:

* every cap-point to lie on the MEC boundary (so
  `arcAngle_chord_length_lt_iff` applies pointwise), which is not
  guaranteed by `CircumscribedMECPacket`; or
* a stronger inscribed-angle argument carrying the strict comparison
  through Thales-form chord-side data alone, which is not in the
  current infrastructure.

The Lc1 docstring (`DumitrescuLc1.lean` §"Open: strict-monotone-distance
form") explicitly leaves this open. The dispatch brief for this file
(2026-05-22) instructs: "if there's a gap, surface it cleanly — do not
introduce sorry".

We therefore split Lc3 into two parts:

* **`lc3_in_cap_iso_bound_weak` (unconditional, proven now).** The
  L2-on-the-cap bound `∑ ≤ mᵢ(mᵢ − 1)`, obtained by applying
  `Problem97.Dumitrescu.base_apex_double_count` (L2) with `A := Cᵢ`
  and `ConvexIndep.mono` to descend `ConvexIndep` to `Cᵢ`. This bound
  is `4 ×` weaker than Cor 1 for large `mᵢ` but is rigorously provable
  from current infrastructure and useful as a fallback.

* **`CapDiagonalVertexProfile` + `lc3_in_cap_iso_bound` (conditional).**
  The structural diagonal-vertex hypothesis — for each apex `a ∈ C`, a
  per-apex iso-pair upper bound `perApex a` summing to at most
  `(C.card − 1)² / 4` — and the bound derived from it. The structure
  is the *combinatorial conclusion* of strict-monotone-distance Lc1;
  constructing one is the open geometric work.

This split mirrors `DumitrescuL5.lean`'s `CapWitnessRanking` pattern:
the geometric input is named explicitly as a structure, downstream
consumers thread it through, and the combinatorial layer is closed.

## What downstream consumers see

L10-final assembly (open) consumes Lc3 via the strong form. Until the
diagonal-vertex argument produces a `CapDiagonalVertexProfile` for
each cap, L10-final remains conditional on the same structural
hypothesis. The weak form `lc3_in_cap_iso_bound_weak` lets L10-final
discharge with a `4 ×` looser final constant (`(11n² − 18n) · 4 / 12`
instead of `(11n² − 18n) / 12`), should a fallback path be needed.

## References

* Adrian Dumitrescu (2006), *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Computational Geometry 36, 503–509. DOI: 10.1007/s00454-006-1262-y. Lemma 2 + Corollary 1, p. 3-4.
* Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, *The Number of Distinct Distances from a Vertex of a Convex Polygon*, Journal of Computational Geometry 4 (2013), 1–12; arXiv:1207.1266 (2012 preprint).
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical




/- ### Unconditional weaker bound (L2-on-the-cap)

Applying `base_apex_double_count` (L2) to `A := Cᵢ` yields the bound
`∑_{a ∈ Cᵢ} |IsoscelesPairsAt(Cᵢ, a)| ≤ Cᵢ.card · (Cᵢ.card − 1)`.

This is unconditional given `ConvexIndep A` (so `ConvexIndep Cᵢ` by
`ConvexIndep.mono`). It is the strongest bound we can prove from the
current Lc1 Thales-form. -/







/- ### Diagonal-vertex hypothesis structure (conditional strong bound)

The diagonal-vertex argument from Dumitrescu §2 p. 3-4 yields the
sharper bound `(Cᵢ.card − 1)² / 4`. The argument requires the
strict-monotone-distance form of Lc1, which is open. We package the
combinatorial conclusion as an explicit structure so the conditional
proof is available now.

A `CapDiagonalVertexProfile C` carries, for each apex `a ∈ C`, a per-
apex upper bound `perApex a` on the iso-pair count at `a`, together
with the *summed* bound `4 · ∑ perApex a ≤ (C.card − 1)²`. The
intended profile is `perApex a = min(j − 1, m − j)` where `j` is
`a`'s 1-indexed arc-position; the sum identity is then `⌊(m − 1)² / 4⌋`.

Constructing a `CapDiagonalVertexProfile` is exactly the work the
strict-monotone-distance Lc1 + arc-order + per-apex pigeonhole would
do. The combinatorial bound `lc3_in_cap_iso_bound` is unconditional
on the structure. -/

theorem Problem97.Dumitrescu.matching_count_sum_le_square_div_four (m : ℕ) :
    ∑ j ∈ Finset.range m, min j (m - 1 - j) ≤ (m - 1)^2 / 4 := by sorry
