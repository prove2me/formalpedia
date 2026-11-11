-- Prove2me | Theorems.Thm_SemiStreamReach_Main_theorem_2
-- name    : SemiStreamReach.Main.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:53:35.991373+00:00
-- url     : https://prove2.me/theorems/f6e879a5-f8a3-4ce4-95f0-20a14ddb04fc
-- title:
--   Theorem 2 — exact single-source shortest paths in $\tilde O(n)$ space and $n^{1/3+o(1)}$ passes
-- statement:
--   In the multi-pass streaming model, a directed graph $G$ on $n$ vertices with nonnegative, polynomially bounded integer edge weights arrives as a stream of its edges in an arbitrary order, the same in every pass; space is measured in bits with words of $O(\log n)$ bits. **Theorem 2.** There is a randomized streaming algorithm that, with high probability, computes exact single-source shortest paths — the distances $\mathrm{dist}_G(s,v)$ for all $v$ ($\infty$ when unreachable) and a shortest-path tree rooted at $s$ — using $\tilde O(n)$ space and $n^{1/3+o(1)}$ passes.
--
--   Precisely: for every $a\in\mathbb N$ and every $c>0$ there are one program $P$ of the randomized word RAM, a word-size constant $c_w$, a constant $A$ and a function $f:\mathbb N\to\mathbb R$ with $f(n)\to0$ such that for every $n\ge1$, every source $s$, every directed graph on $\{0,\dots,n-1\}$ with integer weights in $\{0,\dots,n^a\}$ and every edge order, with word size $c_w\,\ell(n)$ and on every coin tape, the run uses at most
--   $$A\,n\,(\log_2(n+2))^A\ \text{bits at every step and halts within}\ n^{1/3+f(n)}\ \text{passes},$$
--   and the coin tapes on which its output is not the exact distance vector together with a shortest-path tree rooted at $s$ have probability at most $n^{-c}$.
--
--   This is the paper's main result: the best previous semi-streaming algorithm for directed single-source reachability used $n^{1/2+o(1)}$ passes (Jambulapati, Liu and Sidford), and through known reductions (Corollary 3) the result also gives semi-streaming algorithms for bipartite matching, topological sorting and strongly connected components.
--
--   **Formalization Note.** `ExactSSSPSpec` carries the input layout (header $n,s+1$; edges as $u+1,v+1,w$; end marker $0$), the output layout ($2n$ words: distance $+1$ or $0$ for $\infty$, parent $+1$ or $0$), the tree condition (tight parent edges of $G$, and following parents from every reachable vertex reaches $s$), the space charge (every cell ever written) and the failure probability as the measure of the failing coin tapes.
--
--   Differences from the source:
--   - reading: the resource bounds of a randomized algorithm that "with high probability computes …" → space and pass bounds on every coin tape; only correctness is probabilistic; reason: the sentence is ambiguous between bounds on every run and bounds w.h.p.; the every-run reading is the stronger one
--   - reading: Õ(n), n^{1/3+o(1)}, "with high probability", "polynomially bounded" → ∀ a ∀ c > 0 ∃ P cw A f (f → 0): space ≤ A·n·(log₂(n+2))^A, passes ≤ n^{1/3+f(n)}, failure ≤ n^{−c}, weights in {0, …, n^a}; reason: §3 (p. 13) defines Õ and w.h.p.; the proof of Theorem 2 reads polynomially bounded as weights in {0, 1, …, n^a} for a constant a; all constants are fixed before the instance
--   - encoding: a randomized streaming algorithm with O(log n)-bit words; the graph as a stream; the output distances and tree → a DynBrooks.Program, word size cw·ℓ(n); input header n, s + 1, edge words u + 1, v + 1, w, end marker 0; output 2n words (distance + 1 or 0 for ∞, parent + 1 or 0); distances in ℝ≥0∞; space = bits of every cell ever written; failure = coinMeasure of the failing coin tapes; reason: the paper names no instruction set or layout; these are one faithful encoding of each
--   - encoding: a shortest-path tree rooted at s → every reachable v ≠ s has a parent u with (u, v) ∈ E and dist(s, u) + w(u, v) = dist(s, v), and iterating parents from v reaches s; s and unreachable vertices have no parent; reason: with zero weights tight parent edges alone can form a cycle (p. 57, PDF 59); reaching s makes the parent edges a tree of shortest paths
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 2 (PDF 4), Theorem 2; restated p. 14 (PDF 16); proved p. 16 (PDF 18)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_StreamModel

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Theorem 2 (Streaming shortest paths), p. 2 (PDF 4); restated p. 14, proved p. 16 (PDF 18).
"There is a randomized streaming algorithm that, with high probability, computes exact
single-source shortest paths using Õ(n) space and n^{1/3+o(1)} passes in n-vertex directed graphs
with nonnegative, polynomially bounded integer edge weights."

For every weight exponent `a` and every `c > 0` there are one program `P` of the randomized word
RAM, a word-size constant `cw`, a constant `A` and a function `f : ℕ → ℝ` with `f n → 0` such that
for every `n ≥ 1`, every source `s : Fin n`, every directed graph on `Fin n` (edge set `E`, at most
one edge per ordered pair) with integer weights in `{0, …, n^a}` and every order `σ` of its edges:
on the stream with header `n, s + 1`, with word size `cw · ℓ(n)`, on every coin tape the run uses at
most `A · n · (log₂(n + 2))^A` bits at every step and halts having made at most `n^{1/3 + f(n)}`
passes, and the coin tapes on which the output is not the exact distance vector `dist_G(s, ·)`
together with a shortest-path tree rooted at `s` have probability at most `n^{−c}`
(`ExactSSSPSpec`). -/
theorem theorem_2 :
    ∀ (a : ℕ) (c : ℝ), 0 < c →
      ∃ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ) (f : ℕ → ℝ),
        Filter.Tendsto f Filter.atTop (nhds 0) ∧
        ExactSSSPSpec P a cw A (fun n => (n : ℝ) ^ ((1 : ℝ) / 3 + f n))
          (fun n => ENNReal.ofReal ((n : ℝ) ^ (-c))) := by sorry

end SemiStreamReach.Main
