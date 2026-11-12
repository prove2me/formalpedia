-- Prove2me | Theorems.Thm_PDynTreeEmbed_Main_theorem_3_1
-- name    : PDynTreeEmbed.Main.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:32:20.402798+00:00
-- url     : https://prove2.me/theorems/20261b99-86d3-4972-b3de-85186f7a6f22
-- title:
--   Theorem 3.1 — deterministic partially dynamic (1 + ε_SSSP)-approximate SSSP in m^{1+o(1)} total time [BPGS21], [Liu25]
-- statement:
--   For every weight exponent $c_W$ there are $c_0>0$, a deterministic word-RAM program, a word-size constant, $C$ and $f$ with $f(m)\to0$ such that the following holds. Let $G^{(t)}$ be an undirected graph on $n$ vertices with integer edge lengths at most $W\le n^{c_W}$, positive except that edges incident to the fixed source $s$ may have length zero, undergoing only insertions or only deletions, and let $m\ge n$ be the number of edges present initially or inserted. Put $\varepsilon_{SSSP}=2^{-c_0(\log_2 m)^{3/4}}$. On every coin tape, at every time $t$ the maintained estimates satisfy
--   $$\mathrm{dist}_{G^{(t)}}(s,v)\le\tilde d_t(v)\le(1+\varepsilon_{SSSP})\,\mathrm{dist}_{G^{(t)}}(s,v),$$
--   they are nonincreasing under insertions and nondecreasing under deletions, and initialization, all updates and reporting every changed estimate take total time at most $C\,m^{1+f(m)}$. It is the cited tool behind the $m^{1+o(1)}$ running times.
--
--   Differences from the source:
--
--   - reading: ε_SSSP = 2^{−Θ((log m)^{3/4})} → ∃ c₀ > 0 with accuracy 1 + 2^{−c₀(log₂ m)^{3/4}}; reason: the upper half of Θ is the content: a smaller ε only strengthens the guarantee
--   - encoding: a deterministic algorithm → a word-RAM program whose guarantees hold for every coin tape; reason: a program that ignores its coins is one; any such program run on a fixed tape is deterministic
--   - encoding: maintained estimates d̃_t(v), reporting changed estimates → change records (v, q): q = 0 means ∞, q ≥ 1 means q − 1, replayed at each time (estAt); estimates are integers or ∞; reason: rounding a rational estimate down keeps it in [d, (1+ε)d] (d is an integer) and keeps it monotone
--   - encoding: a randomized (or deterministic) algorithm → a program of the published word RAM DynBrooks_Machine with words of a·⌈log₂(n+2)⌉ bits, a fixed with the program; unit-cost uniform random words; read blocks, so updates are seen online; reason: the standard model of the cited SSSP structures; the paper names no model
--   - encoding: the input graph and the update sequence → initialization words n, W, kind, parameter, |E|, edges (u, v, w) in any listing; each update as words delivered to the completed state after the previous one; reason: an encoding; every word fits since W ≤ n^{c_W} and a may be large
--   - encoding: polynomially bounded integer weights → W ≤ n^{c_W} for an arbitrary c_W fixed before the program; constants may depend on c_W; reason: the standing assumption of p. 13
--   - encoding: oblivious adversary → the instance and the whole update sequence are quantified before the coin tape; reason: the definition on p. 3
--   - encoding: initialization, updates, and reporting all changed estimates take total time m^{1+o(1)} → totalTime ≤ C·m^{1+f(m)} on every coin tape, with f : ℕ → ℝ, f(m) → 0, fixed with the program; totalTime counts initialization and every update (reporting included), ∞ if a run does not complete; reason: the meaning of m^{1+o(1)} for a deterministic algorithm
--   - generalization: the standing assumption of §3 that the input graph remains connected → no connectivity hypothesis; unreachable vertices have distance ∞, and the estimate must then be ∞; reason: Theorem 3.1 as printed has no connectivity condition and the paper runs it on auxiliary graphs that need not be connected; a connected graph is a special case
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), p. 13, Theorem 3.1

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_PDynTreeEmbed_Main_Dynamic
open Filter Topology
open scoped ENNReal

namespace PDynTreeEmbed.Main

/-- **Theorem 3.1** ([BPGS21], [Liu25], p. 13). For every weight exponent `c_W` there are `c₀ > 0`, a
deterministic word-RAM program, a word-size constant `a`, a constant `C` and a function `f` with
`f(m) → 0` such that: for every undirected graph `G^(t)` on `n` vertices with integer edge lengths
at most `W ≤ n^{c_W}`, positive except that edges incident to the source `s` may have length zero,
undergoing only insertions or only deletions (fixed in advance), with `m ≥ n` edges present
initially or inserted, and on every coin tape: at every time `t` the maintained estimates satisfy
`d_{G^(t)}(s, v) ≤ d̃_t(v) ≤ (1 + ε_SSSP)·d_{G^(t)}(s, v)` with
`ε_SSSP = 2^{−c₀(log₂ m)^{3/4}}`; the estimates are nonincreasing under insertions and
nondecreasing under deletions; and initialization, all updates and reporting every changed
estimate take total time at most `C·m^{1+f(m)}`. -/
theorem theorem_3_1 : ∀ cW : ℝ, ∃ (c₀ : ℝ) (P : DynBrooks.Program) (a : ℕ) (C : ℝ) (f : ℕ → ℝ),
    0 < c₀ ∧ 0 < C ∧ Tendsto f atTop (𝓝 0) ∧
    ∀ (n W : ℕ) (s : Fin n) (G₀ : WGraph (Fin n)) (κ : Kind) (σ : List (Upd n))
      (es : List (Fin n × Fin n)),
      (W : ℝ) ≤ (n : ℝ) ^ cW → IsSSSPInstance W s G₀ κ σ → n ≤ totalEdges G₀ σ →
      IsEdgeListing G₀ es → ∀ ω : ℕ → BitVec (wordSize a n),
        (∀ t ≤ σ.length, ∀ v : Fin n,
          (graphAt G₀ σ t).dist s v ≤ estAt P ω (initWords W κ s.val G₀ es) σ t v ∧
            (estAt P ω (initWords W κ s.val G₀ es) σ t v : ℝ≥0∞) ≤
              ENNReal.ofReal (1 + (2 : ℝ) ^ (-(c₀ * log2 (totalEdges G₀ σ) ^ ((3 : ℝ) / 4)))) *
                ((graphAt G₀ σ t).dist s v : ℝ≥0∞)) ∧
        (∀ t < σ.length, ∀ v : Fin n,
          (κ = Kind.incr → estAt P ω (initWords W κ s.val G₀ es) σ (t + 1) v ≤
            estAt P ω (initWords W κ s.val G₀ es) σ t v) ∧
          (κ = Kind.decr → estAt P ω (initWords W κ s.val G₀ es) σ t v ≤
            estAt P ω (initWords W κ s.val G₀ es) σ (t + 1) v)) ∧
        (totalTime P ω (initWords W κ s.val G₀ es) σ : ℝ≥0∞) ≤
          ENNReal.ofReal (C * (totalEdges G₀ σ : ℝ) ^ (1 + f (totalEdges G₀ σ))) := by sorry

end PDynTreeEmbed.Main
