-- Prove2me | Theorems.Thm_SemiStreamReach_Main_lemma_28
-- name    : SemiStreamReach.Main.lemma_28
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:52:33.260847+00:00
-- url     : https://prove2.me/theorems/ac036481-41e2-42a2-9e1d-132bcc597004
-- title:
--   Lemma 28 — prefix and suffix are shortcut by single block-closure edges; the middle lies outside all balls
-- statement:
--   In the setting of Claim 27, let $C_p$ be a $(1+\varepsilon)$-approximate block closure of $B_p$ for each pivot $p$ ($\varepsilon\ge0$), let $i$ be the largest index with $v_i$ in the in-ball of some pivot ($-1$ if none) and $j$ the smallest index with $v_j$ in the out-ball of some pivot ($\ell+1$ if none).
--
--   1. For all $0<a\le i$ some $C_p$ contains an edge $(v_0,v_a)$ of weight at most $(1+\varepsilon)\,w(Q[v_0,\dots,v_a])$; for all $j\le a<\ell$ some $C_p$ contains an edge $(v_a,v_\ell)$ of weight at most $(1+\varepsilon)\,w(Q[v_a,\dots,v_\ell])$.
--   2. If $i<j$, the middle subpath $Q[v_{i+1},\dots,v_{j-1}]$ lies in the core subgraph of $G'$ with the empty label: none of its vertices lies in a pivot's in-ball or out-ball.
--   3. If every vertex of $G'$ is a pivot (the last level $r=r_{\max}$), then $$j\le i.$$
--
--   This is what stops type 1 splits from multiplying the pieces at the late levels of the construction.
--
--   Differences from the source:
--   - generalization: Q is a piece of P at a late level r in a subgraph G′ of the recursion, with sampled pivots and radii ρ_p = η_p D_r, η_p ∈ [λ, 2λ) → any graph G′ with positive weights on a finite type, any pivot set Π, any radii ρ_p ≥ 0, any D ≥ 0 and any simple path Q in G′ with w(Q) ≤ D; reason: the proof uses only w(Q) ≤ D_r, ρ_p ≥ 0 and the definitions of the balls and of B_p; the Lean statement specializes to the pieces of the paper
--   - reading: "If r = r_max" → if Π is the whole vertex set; reason: at r_max, LateLevel sets Π ← V(G′) (Algorithm 3, line 19), and item (3) depends on r only through this
--   - encoding: "lies in the core subgraph of G′ with the empty label" → every vertex v_k with i < k < j lies in coreVertices (no pivot's in-ball or out-ball); reason: the core subgraph is induced by these vertices, so it contains the subpath exactly when it contains its vertices
--   - encoding: the closures are those built by the algorithm → any family C with IsApproxBlockClosure for each pivot's block; weights in ℝ≥0∞; reason: every closure the algorithm builds is such a family
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 32 (PDF 34), Lemma 28

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_LateLevel

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Lemma 28 (Prefix, middle, and suffix), p. 32 (PDF 34). Setting of Claim 27; `C p` is a
`(1 + ε)`-approximate block closure of the block `B_p` of each pivot `p`, `i = lastInIdx`,
`j = firstOutIdx`, `ℓ = |Q| − 1`. (1) For `0 < a ≤ i` some closure has an edge `(v_0, v_a)` of
weight at most `(1 + ε) w(Q[v_0, …, v_a])`; for `j ≤ a < ℓ` some closure has an edge `(v_a, v_ℓ)` of
weight at most `(1 + ε) w(Q[v_a, …, v_ℓ])`. (2) If `i < j`, every vertex `v_k` with `i < k < j` lies
in the core subgraph with the empty label. (3) If every vertex is a pivot (`r = r_max`), then
`j ≤ i`. -/
theorem lemma_28 {V : Type*} [Fintype V] (G : WGraph V) (Pi : Set V) (ρ : V → ℝ) (D ε : ℝ)
    (Q : List V) (C : V → WGraph V) (hG : PositiveWeights G) (hρ : ∀ p ∈ Pi, 0 ≤ ρ p)
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hQ : IsPathIn G Q) (hw : walkWeight G Q ≤ ENNReal.ofReal D)
    (hC : ∀ p ∈ Pi, IsApproxBlockClosure G (pivotBlock G p (ρ p) D) ε (C p)) :
    (∀ (a : ℕ) (ha : a < Q.length), 0 < a → (a : ℤ) ≤ lastInIdx G Pi ρ Q →
        ∃ p ∈ Pi, C p (Q[0]'(by omega)) Q[a] ≤
          ENNReal.ofReal (1 + ε) * walkWeight G (Q.take (a + 1))) ∧
      (∀ (a : ℕ) (ha : a < Q.length), firstOutIdx G Pi ρ Q ≤ a → a < Q.length - 1 →
        ∃ p ∈ Pi, C p Q[a] (Q[Q.length - 1]'(by omega)) ≤
          ENNReal.ofReal (1 + ε) * walkWeight G (Q.drop a)) ∧
      (lastInIdx G Pi ρ Q < (firstOutIdx G Pi ρ Q : ℤ) →
        ∀ (k : ℕ) (hk : k < Q.length), lastInIdx G Pi ρ Q < (k : ℤ) →
          k < firstOutIdx G Pi ρ Q → Q[k] ∈ coreVertices G Pi ρ) ∧
      (Pi = Set.univ → (firstOutIdx G Pi ρ Q : ℤ) ≤ lastInIdx G Pi ρ Q) := by sorry

end SemiStreamReach.Main
