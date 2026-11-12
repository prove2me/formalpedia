-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_theorem_1_1
-- name    : PDynTreeEmbed.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:42.129957+00:00
-- url     : https://prove2.me/theorems/00835edf-a9f7-40c3-876f-bef706d8c977
-- title:
--   Theorem 1.1 — partially dynamic LDD with O(log n) slack, Õ(n) expected recourse and m^{1+o(1)} expected total time
-- statement:
--   For every weight exponent $c_W$ and every $c>0$ there are a randomized word-RAM program, a word-size constant, $C$ and $f$ with $f(m)\to0$ such that the following holds. For every connected graph on $n\ge2$ vertices with integer weights in $[1,W]$, $W\le n^{c_W}$, every sequence of only edge insertions or only edge deletions keeping it connected, fixed before the coin tape, and every integer $D\ge1$, the partition the program maintains satisfies: with probability at least $1-n^{-c}$, at every time $t$ every cluster has weak diameter at most $D$ in $G^{(t)}$; for every $t$ and $u,v$,
--   $$\Pr[u,v\ \text{in distinct clusters at time }t]\le C\log_2 n\cdot\frac{\mathrm{dist}_{G^{(t)}}(u,v)}{D};$$
--   the expected total recourse is at most $C\,n\log_2^C n$, and the expected total update time at most $C\,m^{1+f(m)}$. Theorem 1.2's recourse bound applies it at every level.
--
--   Differences from the source:
--
--   - reading: succeeds with high probability → for every c > 0 (fixed before the program) the weak-diameter clause holds at all times with probability ≥ 1 − n^{−c}; the separation, recourse and time clauses hold unconditionally; reason: w.h.p. is the LDD's own clause 1 (p. 2); the other clauses unconditional is the stronger reading
--   - encoding: diameter parameter D > 0 → an integer D ≥ 1, delivered as the word min(D, nW); reason: distances are integers, so weak diameter ≤ D iff ≤ ⌊D⌋ and ⌊D⌋ ≥ D/2 for D ≥ 1 changes only C; D < 1 forces singletons; for D ≥ nW the partition {V} works
--   - encoding: LDD with O(log n) slack → clusters = classes of the replayed labels (labelsAt); slack C·log₂ n; reason: the definition of p. 2
--   - encoding: a randomized (or deterministic) algorithm → a program of the published word RAM DynBrooks_Machine with words of a·⌈log₂(n+2)⌉ bits, a fixed with the program; unit-cost uniform random words; read blocks, so updates are seen online; reason: the standard model of the cited SSSP structures; the paper names no model
--   - encoding: the input graph and the update sequence → initialization words n, W, kind, parameter, |E|, edges (u, v, w) in any listing; each update as words delivered to the completed state after the previous one; reason: an encoding; every word fits since W ≤ n^{c_W} and a may be large
--   - encoding: oblivious adversary → the instance and the whole update sequence are quantified before the coin tape; reason: the definition on p. 3
--   - encoding: polynomially bounded integer weights → W ≤ n^{c_W} for an arbitrary c_W fixed before the program; constants may depend on c_W; reason: the standing assumption of p. 13
--   - encoding: Õ(n) expected total recourse → E[number of words written] ≤ C·n·(log₂ n)^C; reason: Õ(n) = n·polylog n; words and records differ by a factor at most 4
--   - encoding: m^{1+o(1)} expected total update time → E[totalTime] ≤ C·m^{1+f(m)} with f : ℕ → ℝ, f(m) → 0, fixed with the program; totalTime counts initialization and every update, ∞ if a run does not complete; reason: the meaning of m^{1+o(1)}
--   - encoding: n vertices (α = 1/(2 log n) and log n need n ≥ 2) → hypothesis 2 ≤ n; reason: the only excluded case n = 1 makes log₂ n = 0 and α undefined
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 4, Theorem 1.1

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_PDynTreeEmbed_Main_Dynamic
open MeasureTheory Filter Topology
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Theorem 1.1** (Partially Dynamic LDD, p. 4). For every weight exponent `c_W` and every failure
exponent `c > 0` there are a randomized word-RAM program, a word-size constant `a`, a constant `C`
and a function `f` with `f(m) → 0` such that, for every connected graph on `n ≥ 2` vertices with
integer weights in `[1, W]`, `W ≤ n^{c_W}`, every sequence of only insertions or only deletions
(fixed before the coin tape) that keeps it connected, and every integer diameter parameter
`D ≥ 1`, the maintained partition (cluster labels) satisfies: with probability at least `1 − n^{−c}`,
at every time `t` every cluster has weak diameter at most `D` in `G^(t)`; at every time `t` every pair
`u, v` is in distinct clusters with probability at most `C·log₂ n·dist_{G^(t)}(u, v)/D`; the expected
total recourse is at most `C·n·(log₂ n)^C`; and the expected total update time is at most
`C·m^{1+f(m)}`. -/
theorem theorem_1_1 : ∀ cW c : ℝ, 0 < c →
    ∃ (P : DynBrooks.Program) (a : ℕ) (C : ℝ) (f : ℕ → ℝ), 0 < C ∧ Tendsto f atTop (𝓝 0) ∧
    ∀ (n W : ℕ) (G₀ : WGraph (Fin n)) (κ : Kind) (σ : List (Upd n)) (es : List (Fin n × Fin n))
      (D : ℕ), 2 ≤ n → (W : ℝ) ≤ (n : ℝ) ^ cW → IsInstance W G₀ κ σ → IsEdgeListing G₀ es →
      1 ≤ D →
      DynBrooks.coinMeasure (wordSize a n)
          {ω | ∃ t ≤ σ.length, ∃ x y : Fin n,
            labelsAt P ω (initWords W κ (min D (n * W)) G₀ es) σ t x =
              labelsAt P ω (initWords W κ (min D (n * W)) G₀ es) σ t y ∧
            (D : ℕ∞) < (graphAt G₀ σ t).dist x y} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-c)) ∧
      (∀ t ≤ σ.length, ∀ u v : Fin n,
        DynBrooks.coinMeasure (wordSize a n)
            {ω | labelsAt P ω (initWords W κ (min D (n * W)) G₀ es) σ t u ≠
              labelsAt P ω (initWords W κ (min D (n * W)) G₀ es) σ t v} ≤
          ENNReal.ofReal (C * log2 n * (graphAt G₀ σ t).rdist u v / D)) ∧
      ∫⁻ ω, (recourse P ω (initWords W κ (min D (n * W)) G₀ es) σ : ℝ≥0∞)
          ∂(DynBrooks.coinMeasure (wordSize a n)) ≤
        ENNReal.ofReal (C * n * log2 n ^ C) ∧
      ∫⁻ ω, (totalTime P ω (initWords W κ (min D (n * W)) G₀ es) σ : ℝ≥0∞)
          ∂(DynBrooks.coinMeasure (wordSize a n)) ≤
        ENNReal.ofReal (C * (totalEdges G₀ σ : ℝ) ^ (1 + f (totalEdges G₀ σ))) := by sorry

end PDynTreeEmbed.Main
