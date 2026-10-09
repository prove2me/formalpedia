-- Prove2me | Theorems.Thm_TriangleFreeSegments_Probes_theorem_1
-- name    : TriangleFreeSegments.Probes.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:10.077599+00:00
-- url     : https://prove2.me/theorems/460750e6-2bca-4fb6-8986-5f9c3583eba5
-- title:
--   Theorem 1, p. 2 — for every k ≥ 1 some family of plane line segments has no three pairwise intersecting members and χ > k
-- statement:
--   For every integer $k\ge1$ there is a finite family $\mathcal S=(\sigma_i)_{i<N}$ of pairwise distinct line segments in the plane $\mathbb R^2$, each with two distinct endpoints, such that
--
--   1. no three segments of $\mathcal S$ pairwise intersect, i.e. the intersection graph of $\mathcal S$ (vertices the segments, edges the intersecting pairs) is triangle-free, and
--   2. the chromatic number of that intersection graph exceeds $k$:
--   $$
--   \chi(\mathcal S)>k .
--   $$
--
--   This answers negatively Erdős's question whether families of segments in the plane are $\chi$-bounded: triangle-free intersection graphs of segments can have arbitrarily large chromatic number.
--
--   **Formalization Note** Segments are closed segments in `ℝ × ℝ`, the family is indexed by `Fin N`, and the graph is the intersection graph of those actual segments (not an abstract graph). The chromatic number is Mathlib's `chromaticNumber`, valued in $\mathbb N\cup\{\infty\}$, and the conclusion is the literal $\chi>k$.
-- source:
--   Pawlik et al., Triangle-free intersection graphs of line segments with large chromatic number, arXiv:1209.1595v5, p. 2, Theorem 1

import Mathlib
import Definitions.Def_TriangleFreeSegments_Probes_Setting

namespace TriangleFreeSegments.Probes

theorem theorem_1 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : ℕ) (e : Fin N → (ℝ × ℝ) × (ℝ × ℝ)),
      (∀ i, (e i).1 ≠ (e i).2) ∧
      Function.Injective (fun i => seg (e i)) ∧
      (interGraph (fun i => seg (e i))).CliqueFree 3 ∧
      (k : ℕ∞) < (interGraph (fun i => seg (e i))).chromaticNumber := by sorry

end TriangleFreeSegments.Probes
