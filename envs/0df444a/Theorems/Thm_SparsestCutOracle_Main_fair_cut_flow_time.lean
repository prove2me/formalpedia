-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_fair_cut_flow_time
-- name    : SparsestCutOracle.Main.fair_cut_flow_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:51.629421+00:00
-- url     : https://prove2.me/theorems/f94b8a9f-5567-4d12-82b5-f3fdec10568f
-- title:
--   Theorem 3 — FairCutFlow (corrected: 1 < ω ≤ 2)
-- statement:
--   For a connected loopless graph with positive real edge capacities and nonnegative vertex weights $s,t$, let $W_G$ be total capacity divided by minimum capacity. For every $1<\omega\le2$ and every failure exponent $a$, one charged program returns an $\omega$-fair $(s,t)$ cut/flow pair with probability at least $1-n^{-a}$. There are $C>0$ and a natural exponent $c$, fixed before the input, such that every tape halts within
--
--   $$C\frac{m}{(\omega-1)^3}(1+\log W_G)(\log n)^c$$
--
--   units of work. The output stores a cut and one signed flow value per edge. This is the paper's stated fair-flow black box, not a terminal-cut-only oracle.
--
--   Differences from the source:
--   - correction: ω ≥ 1 and time Õ(m/(ω−1)^3 log W_G) → 1 < ω ≤ 2; reason: at ω=1 the denominator vanishes; for a fixed nontrivial graph and arbitrarily large ω the uniform upper bound becomes smaller than the charged halt instruction; the paper uses only ω=2
--   - reading: a randomized algorithm, with no machine specified → one finite admissible charged real-RAM program with square roots and independent standard Gaussian and fair-coin tapes; reason: the base machine is the published ClusterDecomp machine; the only new scalar instructions are square root and Gaussian sampling
--   - reading: with high probability → for every natural exponent a, a measurable event of probability at least 1 − n^(−a); reason: the program and time constants may depend on a; qualitative approximation constants precede a
--   - encoding: finite vertices and nonnegative real capacities → vertices Fin n and loopless edge lists with nonnegative real capacities; parallel entries are retained; reason: the edge list is the input and m is its length; summing parallel entries gives the same cut capacities
--   - encoding: log W_G and a ratio of total to minimum edge weight → 1 + log W_G, positive listed capacities, and n ≥ 2; reason: the ratio is defined on these inputs and W_G=1 must not force zero running time
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 9, Theorem 3 ([LNPS23])

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_FairFlow

namespace SparsestCutOracle.Main

/-- Theorem 3, p.9. Corrected fairness range: 1<ω≤2. All-tape running-time bound. -/
theorem fair_cut_flow_time :
    ∀ a : ℕ, ∃ P : Program, Admissible P ∧ ∃ c : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : Graph n) (s t : Fin n → ℝ) (ω : ℝ),
        2 ≤ n → G.NoLoops → G.Connected → (∀ e ∈ G, 0 < (e.capacity : ℝ)) →
        (∀ v, 0 ≤ s v) → (∀ v, 0 ≤ t v) → 1 < ω → ω ≤ 2 →
        let input := fairState G s t ω
        (∀ tape : Tape, ∃ k : ℕ, (run P input tape k).base.halted = true ∧
          ((run P input tape k).base.work : ℝ) ≤
            C * (G.length : ℝ) / (ω - 1) ^ 3 *
              (1 + Real.log G.capacityRatio) * Real.log n ^ c) ∧
        HighProbability n a P input
          (fun out => FairPair G.toWGraph s t ω (outputCut n out) (outputFlow G out)) := by sorry

end SparsestCutOracle.Main
