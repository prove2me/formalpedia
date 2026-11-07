-- Prove2me | Theorems.Thm_RealAPSP_theorem_1_1
-- name    : RealAPSP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:37.839133+00:00
-- url     : https://prove2.me/theorems/581517ad-4ec1-4fb9-b08b-0292a1d76c7f
-- title:
--   Theorem 1.1 (Real-to-Integer Reduction for APSP)
-- statement:
--   Let $d\ge0$ be an integer. There is $c>0$ such that for every $\varepsilon>0$: if Integer APSP with edge weights from $\{-u,\dots,u\}$ can be solved in time $O(n^{3-\varepsilon}(\log(u+2))^d)$, then Real APSP can be solved in time
--
--   $$O(n^{3-c\varepsilon^3}),$$
--
--   by a randomized algorithm correct with high probability, in the comparison-addition model.
--
--   So for APSP, anything achievable in truly subcubic time with integer-only techniques applies to real weights as well. The paper notes that both sides of the implication are now known to hold unconditionally, by Alman and Vassilevska Williams; the theorem is of interest for its black-box reduction, which is combinatorial.
--
--   **Formalization Note** The machine is `RealAPSP.Machine`, and the two sides are `RealAPSP.IntegerAPSPSolved` and `RealAPSP.RealAPSPSolved`.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - reading: randomized algorithm with high probability (§3.1, p.9) → for every failure exponent a there is a program, with the time bound on every tape and correctness on a measurable set of tapes of probability at least 1 − n^{−a}; reason: the p.9 definition, with worst-case time because the page bounds the running time without an expectation
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: (log u)^{O(1)} → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - reading: (log u)^{O(1)} and Ω(ε³), with the order of their constants unstated → ∀ d ∃ c > 0 ∀ ε > 0: the saving depends on the polylog exponent d; reason: the printed proof feeds log u = (s log r)^{O(1)} to the assumed algorithm, so "s sufficiently small" (pp.19, 20, 24) depends on d; no argument in the paper gives c independent of d
--   - reading: "can be solved in time" on the integer side, "by a randomized algorithm" only on the real side → a deterministic hypothesis: the integer run is on the all-false tape; reason: the wording marks only the conclusion as randomized, and p.1 contrasts the deterministic integer algorithm with the randomized real one
--   - reading: word RAM on integer inputs from {−u, …, u} → one machine with word bound ((n+2)(u+2))^c, u in a cell, one program for all u, reals unused; reason: words of O(log n + log u) bits, so weights fit in a word; a word RAM on such words is simulated at polylog overhead
--   - encoding: "a directed graph", number of nodes n → an adjacency matrix with ⊥ for a non-edge, and n ≥ 1; reason: parallel arcs would make a bound in n alone false; O(n^r) is 0 at n = 0
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Theorem 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_RealAPSP_Problems

namespace RealAPSP

/-- **Theorem 1.1 (Real-to-Integer Reduction for APSP).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.2 (PDF p.4).

For every polylog exponent `d` there is `c > 0` such that for every `ε > 0`: if Integer APSP with weights from `{−u, …, u}` is solved
deterministically in time `O(n^{3−ε} (log(u+2))^d)`, then Real APSP is solved in time `O(n^{3−cε³})` by a randomized algorithm correct with high probability.

**Formalization Note.** The machine, its word bounds and the time and success forms are in `RealAPSP.Machine` and `RealAPSP.Problems`. The saving `c` depends on `d` and on
nothing else. It is chosen before `ε`, and before the failure exponent inside `RealAPSPSolved`. -/
theorem theorem_1_1 :
    ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → IntegerAPSPSolved ε d → RealAPSPSolved (3 - c * ε ^ 3) := by sorry

end RealAPSP
