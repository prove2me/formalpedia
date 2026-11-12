-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_theorem_1_2
-- name    : PDynTreeEmbed.Main.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:36.448213+00:00
-- url     : https://prove2.me/theorems/c9d18daf-69e0-4251-9f7a-5a73c346e60f
-- title:
--   Theorem 1.2 — partially dynamic O(log n)-approximate tree embedding with Õ(n) expected recourse and m^{1+o(1)} expected total time
-- statement:
--   For every weight exponent $c_W$ there are a randomized word-RAM program, a word-size constant $a$, a constant $C$ and a function $f$ with $f(m)\to0$ such that the following holds. For every connected graph $G=(V,E,w)$ on $n\ge2$ vertices with integer weights in $[1,W]$, $W\le n^{c_W}$, and every sequence of only edge insertions or only edge deletions that keeps it connected, fixed before the coin tape (an oblivious adversary), the tree $T^{(t)}$ the program maintains satisfies at every time $t$: on almost every tape $T^{(t)}$ is a tree with $V\subseteq V(T^{(t)})$ and $\mathrm{dist}_{T^{(t)}}(u,v)\ge\mathrm{dist}_{G^{(t)}}(u,v)$, and
--   $$\mathbb E\big[\mathrm{dist}_{T^{(t)}}(u,v)\big]\le C\log_2 n\cdot\mathrm{dist}_{G^{(t)}}(u,v)\qquad\text{for all }u,v\in V;$$
--   the expected total recourse is at most $C\,n\log_2^C n$ and the expected total update time is at most $C\,m^{1+f(m)}$. This is the paper's headline result.
--
--   Differences from the source:
--
--   - reading: the algorithm succeeds with high probability → every clause is stated unconditionally on the coin-tape law; reason: implies the w.h.p. reading (take the success event to be everything) and is achievable: on the paper's initialization failure (p. 24, footnote 6) a program can output a star with large weights
--   - encoding: dist_T(u, v) ≥ dist_G(u, v) for every T ∈ supp(𝒯) → for almost every coin tape; reason: exact sampling may need loops that fail only on null sets of tapes
--   - encoding: maintains an O(log n)-approximate probabilistic tree embedding → the tree replayed from change records (treeAt): nodes ℕ, vertex v is node v, tree on its node set; expected stretch C·log₂ n for every pair at every time; reason: 'maintains' means the program writes the object; the definition of p. 2
--   - encoding: a randomized (or deterministic) algorithm → a program of the published word RAM DynBrooks_Machine with words of a·⌈log₂(n+2)⌉ bits, a fixed with the program; unit-cost uniform random words; read blocks, so updates are seen online; reason: the standard model of the cited SSSP structures; the paper names no model
--   - encoding: the input graph and the update sequence → initialization words n, W, kind, parameter, |E|, edges (u, v, w) in any listing; each update as words delivered to the completed state after the previous one; reason: an encoding; every word fits since W ≤ n^{c_W} and a may be large
--   - encoding: oblivious adversary → the instance and the whole update sequence are quantified before the coin tape; reason: the definition on p. 3
--   - encoding: polynomially bounded integer weights → W ≤ n^{c_W} for an arbitrary c_W fixed before the program; constants may depend on c_W; reason: the standing assumption of p. 13
--   - encoding: Õ(n) expected total recourse → E[number of words written] ≤ C·n·(log₂ n)^C; reason: Õ(n) = n·polylog n; words and records differ by a factor at most 4
--   - encoding: m^{1+o(1)} expected total update time → E[totalTime] ≤ C·m^{1+f(m)} with f : ℕ → ℝ, f(m) → 0, fixed with the program; totalTime counts initialization and every update, ∞ if a run does not complete; reason: the meaning of m^{1+o(1)}
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 4, Theorem 1.2

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_PDynTreeEmbed_Main_Dynamic
open MeasureTheory Filter Topology
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Theorem 1.2** (Partially Dynamic Tree Embedding, p. 4). For every weight exponent `c_W` there
are a randomized word-RAM program, a word-size constant `a`, a constant `C` and a function `f` with
`f(m) → 0` such that, for every connected graph on `n ≥ 2` vertices with integer weights in
`[1, W]`, `W ≤ n^{c_W}`, and every sequence of only insertions or only deletions (fixed before the
coin tape) that keeps it connected, the tree `T^(t)` the program maintains through its change
records satisfies, at every time `t`: on almost every tape `T^(t)` is a tree containing `V` with
`dist_{T^(t)}(u, v) ≥ dist_{G^(t)}(u, v)` for all `u, v`, and
`E[dist_{T^(t)}(u, v)] ≤ C·log₂ n·dist_{G^(t)}(u, v)` for all `u, v`; the expected total recourse is
at most `C·n·(log₂ n)^C`; and the expected total update time is at most `C·m^{1+f(m)}`. -/
theorem theorem_1_2 : ∀ cW : ℝ,
    ∃ (P : DynBrooks.Program) (a : ℕ) (C : ℝ) (f : ℕ → ℝ), 0 < C ∧ Tendsto f atTop (𝓝 0) ∧
    ∀ (n W : ℕ) (G₀ : WGraph (Fin n)) (κ : Kind) (σ : List (Upd n)) (es : List (Fin n × Fin n)),
      2 ≤ n → (W : ℝ) ≤ (n : ℝ) ^ cW → IsInstance W G₀ κ σ → IsEdgeListing G₀ es →
      (∀ t ≤ σ.length, ∀ᵐ ω ∂(DynBrooks.coinMeasure (wordSize a n)),
        (treeAt P ω (initWords W κ 0 G₀ es) σ t).toWGraph.IsTreeOn
            ((treeAt P ω (initWords W κ 0 G₀ es) σ t).nodes : Set ℕ) ∧
          ∀ u v : Fin n, (graphAt G₀ σ t).dist u v ≤
            (treeAt P ω (initWords W κ 0 G₀ es) σ t).toWGraph.dist u.val v.val) ∧
      (∀ t ≤ σ.length, ∀ u v : Fin n,
        ∫⁻ ω, ((treeAt P ω (initWords W κ 0 G₀ es) σ t).toWGraph.dist u.val v.val : ℝ≥0∞)
            ∂(DynBrooks.coinMeasure (wordSize a n)) ≤
          ENNReal.ofReal (C * log2 n) * ((graphAt G₀ σ t).dist u v : ℝ≥0∞)) ∧
      ∫⁻ ω, (recourse P ω (initWords W κ 0 G₀ es) σ : ℝ≥0∞)
          ∂(DynBrooks.coinMeasure (wordSize a n)) ≤
        ENNReal.ofReal (C * n * log2 n ^ C) ∧
      ∫⁻ ω, (totalTime P ω (initWords W κ 0 G₀ es) σ : ℝ≥0∞)
          ∂(DynBrooks.coinMeasure (wordSize a n)) ≤
        ENNReal.ofReal (C * (totalEdges G₀ σ : ℝ) ^ (1 + f (totalEdges G₀ σ))) := by sorry

end PDynTreeEmbed.Main
