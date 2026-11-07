-- Prove2me | Theorems.Thm_PunctSketch_coordinator_queries
-- name    : PunctSketch.coordinator_queries
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:19.2502+00:00
-- url     : https://prove2.me/theorems/104a1d91-ed48-488f-b2c9-b0b78da324dd
-- title:
--   §5.4, p.22 — query count and failure handling for any oracle
-- statement:
--   Let $1\le k<n$ and let $\mathcal T$ be any oracle. Along any run of the coordinator's procedure, with any pair order,
--   $$|E(H)|+\binom{k+1}{2}\le kn,\qquad\#\{\text{evaluations of }\mathcal T\}+\binom{k+1}{2}\le\binom n2+kn.$$
--   A state that has not failed and has pairs left has a next step, and there is no infinite run. So the procedure stops, reports failure, or finishes the pairs, even when the event $\mathcal E$ does not occur.
--
--   Differences from the source:
--   - encoding: at most (n choose 2) + kn − (k+1 choose 2) = O(n²) times → additive form, without the O(n²); reason: no natural-number subtraction; O(n²) follows for k < n
--   - reading: "it stops", "step 4 can still be performed" → no infinite run, and each non-failed state with pairs left has a next step; reason: this is what the sentences say for the transition relation; running time is carried by the machine clause of the goal
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.4, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_PunctSketch_CoordStep

namespace PunctSketch

/-- **Query count and failure handling.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4, p.22: "Each computation of 𝒯(F) either adds an
edge to H or finishes processing a pair. Since H has at most kn − (k+1 choose 2) edges, the coordinator
computes 𝒯(F) at most (n choose 2) + kn − (k+1 choose 2) = O(n²) times"; "So it stops and reports failure
if the procedure returns FAIL, or if 𝒯(F) is not a forest on V ⧵ F. Otherwise, step 4 can still be
performed."

For **any** oracle `𝒯`, along any run: `|E(H)| ≤ k n − (k+1 choose 2)` and the number of evaluations of
`𝒯` is at most `(n choose 2) + k n − (k+1 choose 2)`. A state that has not failed and has pairs left has
a next step, and there is no infinite run.

**Formalization Note.** The bounds are written additively. Polynomial running time is carried by the
machine clause of the goal. -/
theorem coordinator_queries {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (𝒯 : Finset (Fin n) → Option (Finset (Sym2 (Fin n))))
    (pairs : List (Fin n × Fin n)) (hpairs : IsPairOrder pairs) :
    (∀ s : CoordState n, Relation.ReflTransGen (CoordStep 𝒯 k) (coordInit pairs) s →
      s.H.edgeSet.ncard + (k + 1).choose 2 ≤ k * n ∧
      s.queries + (k + 1).choose 2 ≤ n.choose 2 + k * n ∧
      (s.failed = false → s.pairs ≠ [] → ∃ s', CoordStep 𝒯 k s s')) ∧
    ¬ ∃ f : ℕ → CoordState n, f 0 = coordInit pairs ∧ ∀ i, CoordStep 𝒯 k (f i) (f (i + 1)) := by sorry

end PunctSketch
