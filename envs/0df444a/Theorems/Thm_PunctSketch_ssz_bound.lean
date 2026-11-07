-- Prove2me | Theorems.Thm_PunctSketch_ssz_bound
-- name    : PunctSketch.ssz_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:10.231621+00:00
-- url     : https://prove2.me/theorems/7fce45a1-087b-4fc5-b13c-7180b4c7f234
-- title:
--   §5.4, p.21 — the [SSZ09] edge bound $kn-\binom{k+1}{2}$
-- statement:
--   Let $1\le k<n$. Consider a sequence of edges added one at a time to the empty graph on $n$ vertices, where each added edge $\{x,y\}$ joins two vertices that some set $F$ with $|F|<k$, $x,y\notin F$, separates in the current graph. Then the number $m$ of edges satisfies
--   $$m+\binom{k+1}{2}\le kn.$$
--   This is what bounds the size of the certificate, whatever the oracle answers.
--
--   Differences from the source:
--   - reading: "Sorkin, Steger and Zenklusen [SSZ09] show", a cited result → stated as a theorem to be proved here; reason: the paper does not prove it, and the mission’s goal rests on it
--   - encoding: at most kn − (k+1 choose 2) edges, for 1 ≤ k < n (conventions, p.4) → m + (k+1 choose 2) ≤ k n, with 1 ≤ k < n as hypotheses; reason: no natural-number subtraction; same statement
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.4, p.21 (PDF p.22), citing [SSZ09]

import Mathlib
import Definitions.Def_PunctSketch_edgesGraph
import Definitions.Def_PunctSketch_CoordStep

namespace PunctSketch

/-- **The [SSZ09] edge bound.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4, p.21: "Sorkin, Steger and Zenklusen [SSZ09] show that any
graph built by adding such edges has at most kn − (k+1 choose 2) edges."

On `n` vertices with `1 ≤ k < n`: a sequence of edges added from the empty graph, each joining two
vertices that some set of fewer than `k` vertices separates in the current graph, has at most
`k n − (k+1 choose 2)` edges.

**Formalization Note.** The bound is written additively. This is cited in the paper, not proved there. -/
theorem ssz_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (es : List (Fin n × Fin n))
    (h : ∀ (i : ℕ) (hi : i < es.length), ∃ F : Finset (Fin n), F.card < k ∧
      Separates (edgesGraph (es.take i)) F es[i].1 es[i].2) :
    es.length + (k + 1).choose 2 ≤ k * n := by sorry

end PunctSketch
