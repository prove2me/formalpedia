-- Prove2me | Theorems.Thm_RealAPSP_sec_3_2_reductions
-- name    : RealAPSP.sec_3_2_reductions
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:42.801375+00:00
-- url     : https://prove2.me/theorems/58f9fecc-05ec-4850-9a7a-bd9a67bf635d
-- title:
--   §3.2 — APSP and Negative Triangle are subcubically equivalent, for integers and for reals
-- statement:
--   Integer APSP and Integer Negative Triangle are subcubically equivalent, and so are Real APSP and Real Negative Triangle. Precisely:
--
--   1. If Integer APSP is solved in time $O(n^{3-\varepsilon}(\log(u+2))^d)$, then Integer Negative Triangle is decided in the same time bound.
--   2. If Integer Negative Triangle is decided in time $O(n^{3-\varepsilon}(\log(u+2))^d)$ with $\varepsilon>0$, then Integer APSP is solved in time $O(n^{3-\varepsilon'}(\log(u+2))^{d'})$ for some $\varepsilon'>0$ and $d'$.
--   3. There is an absolute $c_1>0$ such that for $\delta>0$, Real Negative Triangle in time $O(n^{3-\delta})$ gives Real APSP in time $O(n^{3-c_1\delta})$.
--   4. Real APSP in time $O(n^r)$ gives Real Negative Triangle in time $O(n^r)$.
--
--   The paper cites these from Vassilevska Williams and Williams; the real reduction avoids a binary search over triangle weights. Clauses 1 and 3 are the directions the proof of Theorem 1.1 uses.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - generalization: subcubic equivalence, with no exponents stated → clauses 1, 3 and 4 fix how the exponent moves; reason: each clause implies its direction of the printed equivalence, and these are the known forms of [VWW18]
--   - reading: randomized algorithm with high probability (§3.1, p.9) → for every failure exponent a there is a program, with the time bound on every tape and correctness on a measurable set of tapes of probability at least 1 − n^{−a}; reason: the p.9 definition, with worst-case time because the page bounds the running time without an expectation
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: (log u)^{O(1)} → the logarithm of the argument plus 2; reason: the page writes O-notation for large arguments; the literal formula is 0 at small arguments, where a machine needs at least one step
--   - encoding: a graph or matrices on n nodes, n unrestricted → 1 ≤ n inside IntegerAPSPSolved, RealAPSPSolved, IntNegTriDecided, RealNegTriSolved; reason: O(n^r) is 0 at n = 0, where the instance is empty
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), §3.2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_RealAPSP_Problems

namespace RealAPSP

/-- **§3.2, p.10 (PDF p.12): APSP and Negative Triangle are subcubically equivalent, for integers and for reals.** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…). Cited in the paper from [VWW18].

The four clauses are: (1) Integer APSP in a time bound gives Integer Negative Triangle in the same bound; (2) truly subcubic Integer Negative Triangle gives truly
subcubic Integer APSP; (3) Real Negative Triangle with saving `δ` gives Real APSP with saving `c₁·δ`, for one absolute `c₁`; (4) Real APSP in time `O(n^r)` gives Real Negative
Triangle in time `O(n^r)`. Clauses (1) and (3) are the directions the proof of Theorem 1.1 uses. -/
theorem sec_3_2_reductions :
    (∀ (ε : ℝ) (d : ℕ), 0 < ε → IntegerAPSPSolved ε d → IntNegTriDecided ε d) ∧
    (∀ (ε : ℝ) (d : ℕ), 0 < ε → IntNegTriDecided ε d → ∃ (ε' : ℝ) (d' : ℕ), 0 < ε' ∧ IntegerAPSPSolved ε' d') ∧
    (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ δ : ℝ, 0 < δ → RealNegTriSolved (3 - δ) → RealAPSPSolved (3 - c₁ * δ)) ∧
    (∀ r : ℝ, RealAPSPSolved r → RealNegTriSolved r) := by sorry

end RealAPSP
