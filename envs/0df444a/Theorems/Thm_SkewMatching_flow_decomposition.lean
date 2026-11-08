-- Prove2me | Theorems.Thm_SkewMatching_flow_decomposition
-- name    : SkewMatching.flow_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:43.703042+00:00
-- url     : https://prove2.me/theorems/28b9dfad-4aa1-41d4-b36b-3d630174655f
-- title:
--   §3.5, p.9 — decomposition of an integral symmetric flow into regular paths and cycles
-- statement:
--   Let $f$ be an integral symmetric flow from $s$ to $s'$ in a finite skew-symmetric graph. Then the edges with $f_e=1$ split into three families, pairwise edge-disjoint: regular paths from $s$ to $s'$, regular paths from $s'$ to $s$, and regular cycles. Moreover
--
--   $$
--   |f|=\#\{s\to s'\text{ paths}\}-\#\{s'\to s\text{ paths}\}.
--   $$
--
--   This is the tool behind Lemma 15. The paper cites it to Goldberg and Karzanov.
--
--   Differences from the source:
--   - encoding: split f into a set of paths and cycles → three lists, together edge-disjoint, whose edges are exactly the support of f; reason: at unit capacity a split is a partition of the support
--   - reading: the printed sentence names no value → the value equals the count of s→s′ paths minus the count of s′→s paths; reason: this is how the proof of Lemma 15 uses the decomposition: a path contributes 1 or −1 to the flow value
--   - encoding: a path → a vertex-simple path; reason: a regular walk contains a vertex-simple regular path, so existence is unchanged
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), proof of Lemma 15, p.9 (cited to [GK04])

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph_IsFlow
import Definitions.Def_SkewMatching_SkewGraph_IsRegularPathIn

namespace SkewMatching

/-- **Flow decomposition**, §3.5, p.9. "By the flow decomposition theorem of skew-symmetric flows ([GK04]), we can split f into a set of regular paths from s to s′ or from s′ to s, with additional regular cycles that do not use both an edge and its symmetric edge
simultaneously."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), proof of Lemma 15, p.9 (cited to [GK04], no proof in the paper).

**Formalization Note.** The three families are together edge-disjoint and their edges are exactly the support of `f` (values are at most `1`, so this is the sum of indicators). The value is the number of `s → s′` paths minus the number of `s′ → s` paths, the count
used in the proof of Lemma 15. -/
theorem flow_decomposition {V E : Type*} [Fintype V] [Fintype E] (G : SkewGraph V E) (s : V)
    (f : E → ℕ) (hf : G.IsFlow s f) :
    ∃ paths revPaths cycles : List (List E),
      (∀ p ∈ paths, G.IsRegularPathIn Finset.univ s (G.σV s) p) ∧
      (∀ p ∈ revPaths, G.IsRegularPathIn Finset.univ (G.σV s) s p) ∧
      (∀ p ∈ cycles, G.IsRegularCycleIn Finset.univ p) ∧
      (paths ++ revPaths ++ cycles).flatten.Nodup ∧
      (∀ e, f e = 1 ↔ e ∈ (paths ++ revPaths ++ cycles).flatten) ∧
      G.value s f = (paths.length : ℤ) - (revPaths.length : ℤ) := by sorry

end SkewMatching
