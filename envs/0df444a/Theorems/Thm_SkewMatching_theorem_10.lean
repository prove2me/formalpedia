-- Prove2me | Theorems.Thm_SkewMatching_theorem_10
-- name    : SkewMatching.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:53.088293+00:00
-- url     : https://prove2.me/theorems/f07db7e3-9869-4349-8d16-d65c14510106
-- title:
--   Theorem 10 — optimality and augmentation of integral symmetric flows
-- statement:
--   Let $G$ be a finite skew-symmetric graph with unit capacities and $f$ an integral symmetric flow from $s$ to $s'$. Write $R_f$ for the residual graph of $f$.
--
--   1. The flow $f$ is maximum if and only if there is no regular path from $s$ to $s'$ in $R_f$.
--   2. If $p$ is a regular path from $s$ to $s'$ in $R_f$, then augmenting along $p$ and its symmetric path gives an integral symmetric flow of larger value.
--
--   This turns maximum symmetric flow into repeated search for regular paths. The paper cites it to Goldberg and Karzanov.
--
--   Differences from the source:
--   - encoding: the residual graph → the active edges G.active f of G.doubled; reason: the same edges with the same ends and symmetry; the doubled graph does not depend on f
--   - encoding: a path → a vertex-simple path; reason: a regular walk contains a vertex-simple regular path, so existence is unchanged
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 10, p.4 (cited to [GK96, GK04])

import Mathlib
import Definitions.Def_SkewMatching_Partition
import Definitions.Def_SkewMatching_SkewGraph_IsFlow
import Definitions.Def_SkewMatching_SkewGraph_doubled

namespace SkewMatching

/-- **Theorem 10**, p.4. "Given an skew-symmetric graph G with edge capacity 1 and an integral symmetric flow f on G, • The flow f is maximum if and only if there is no regular path from s to s′ in this
residual graph. • If there is a regular path from s to s′, augmenting one unit along it and its symmetric path gives an integral symmetric flow of larger value."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 10, p.4 (cited to [GK96, GK04], no proof in the paper).

**Formalization Note.** The residual graph of `f` is the sub-multigraph `SkewGraph.active f` of `G.doubled`. Both bullets are stated, for every finite `G`. -/
theorem theorem_10 {V E : Type*} [Fintype V] [Fintype E] (G : SkewGraph V E) (s : V) (f : E → ℕ)
    (hf : G.IsFlow s f) :
    (G.IsMaxFlow s f ↔ ¬ ∃ p, G.doubled.IsRegularPathIn (SkewGraph.active f) s (G.σV s) p) ∧
      ∀ p, G.doubled.IsRegularPathIn (SkewGraph.active f) s (G.σV s) p →
        G.IsFlow s (G.augment f p) ∧ G.value s f < G.value s (G.augment f p) := by sorry

end SkewMatching
