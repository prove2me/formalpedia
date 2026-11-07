-- Prove2me | Theorems.Thm_VertexSampleCSP_lemma_A_1
-- name    : VertexSampleCSP.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:35.736347+00:00
-- url     : https://prove2.me/theorems/eea1a667-aaef-4325-8cae-4b20f3eab1cf
-- title:
--   Lemma A.1, p.14 — $d_H(U,V)=\sup_{u\in B_2^D}|h_U(u)-h_V(u)|$ for nonempty compact convex sets
-- statement:
--   Let $U,V\subseteq\mathbb R^D$ be nonempty, compact and convex, with support functions $h_U,h_V$, and let $B_2^D$ be the closed Euclidean unit ball. Then
--
--   $$d_H(U,V)=\sup_{u\in B_2^D}|h_U(u)-h_V(u)|.$$
--
--   This identity turns the Hausdorff distance between sums of polytopes into a supremum of a sum of real-valued functions, which is what a Rademacher argument can act on.
--
--   **Formalization Note** $d_H$ is `Metric.hausdorffDist`, which on nonempty compact sets is the max–min formula of p.13. The supremum is stated as a least upper bound, so boundedness of the values is part of the claim.
--
--   Differences from the source:
--
--   - encoding: ℝ^D → EuclideanSpace ℝ ι for a finite index type ι; reason: same spaces up to the name of the index set
--   - encoding: d_H = sup → IsLUB of the image of the closed unit ball with value Metric.hausdorffDist; reason: the sup of a bounded nonempty set; no default value can enter
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma A.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_VertexSampleCSP_supportFn
open scoped InnerProductSpace

namespace VertexSampleCSP

/-- **Lemma A.1 (Hausdorff distance by support functions).** Chang, *Optimal Vertex Sampling for
Constraint Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma A.1,
p.14 (PDF p.16): "For nonempty compact convex sets U, V ⊆ ℝ^D, dH(U, V) = sup_{u∈B^D_2} |hU(u) − hV(u)|."

For nonempty compact convex sets `U, W` of the Euclidean space `ℝ^ι`, the Hausdorff distance
`d_H(U, W)` is the least upper bound of `|h_U(u) − h_W(u)|` over the closed unit ball.

**Formalization Note.** `ℝ^D` is `EuclideanSpace ℝ ι` for a finite index type `ι`. `d_H` is
`Metric.hausdorffDist`, which on nonempty compact sets equals the paper's max–min formula (p.13).
The supremum is stated as `IsLUB`, so the set of values is bounded and its supremum is `d_H(U, W)`:
no junk value of a real `sSup` can enter. -/
theorem lemma_A_1 {ι : Type*} [Fintype ι] (U W : Set (EuclideanSpace ℝ ι))
    (hU : U.Nonempty) (hUc : IsCompact U) (hUcv : Convex ℝ U)
    (hW : W.Nonempty) (hWc : IsCompact W) (hWcv : Convex ℝ W) :
    IsLUB ((fun u => |supportFn U u - supportFn W u|) '' Metric.closedBall 0 1)
      (Metric.hausdorffDist U W) := by sorry

end VertexSampleCSP
