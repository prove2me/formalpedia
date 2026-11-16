-- Prove2me | Theorems.Thm_RealAPSP_Supplement_theorem_1_3
-- name    : RealAPSP.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:04:07.024313+00:00
-- url     : https://prove2.me/theorems/a7fb5027-2614-4bcd-af11-2ded0274c546
-- title:
--   Theorem 1.3 — an $O(n^{3-\epsilon}(\log u)^{O(1)})$ Integer Exact Triangle algorithm yields a randomized $O(n^{3-\Omega(\epsilon^2)})$ Real Exact Triangle algorithm
-- statement:
--   This is the real-to-integer reduction for Exact Triangle.
--
--   Work in the comparison-addition model: a word RAM whose real registers support only additions, negations and comparisons. For every $d\in\mathbb N$ there is a constant $c>0$ such that for every $\epsilon>0$ the following holds. Suppose Integer Exact Triangle on $n\times n$ matrices with weights in $\{-u,\dots,u\}$ and missing entries $\bot$ allowed is solved by a deterministic algorithm in time
--
--   $$O\big(n^{3-\epsilon}(\log(u+2))^{d}\big),$$
--
--   with one algorithm for all $n$ and $u$. Then Real Exact Triangle (with $\bot$ allowed) is solved in time
--
--   $$O\big(n^{3-c\epsilon^{2}}\big)$$
--
--   by a randomized algorithm correct with high probability, that is, with failure probability at most $n^{-a}$ for a failure exponent $a$ that can be chosen arbitrarily large.
--
--   Exact Triangle asks whether there are $i,k,j\in[n]$ with $A[i,k]+B[k,j]+C[i,j]=0$, all three entries present. The theorem shows that integer-specific techniques for Exact Triangle carry over to real inputs, with a polynomially smaller saving in the exponent. It is the equality-constraint warm-up to the paper's main result for APSP.
--
--   **Formalization Note** The time classes are `IntExactTriDecided` and `RealExactTriSolved` from the supplement's definitions. The saving constant $c$ depends only on the polylog exponent $d$ and is chosen before $\epsilon$, as in the published Theorem 1.1. The time constant of the real algorithm may depend on the failure exponent.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the published machine RealAPSP.Machine: unit cost, word bound width^c, fair coins preloaded in memory; reason: as in the published Theorem 1.1: the realistic variant defers to [FPS26, Section 1.1], which is not held, and the theorem does not name it
--   - reading: (log u)^{O(1)} and Ω(ε²), with the order of their constants unstated → ∀ d ∃ c > 0 ∀ ε > 0: the saving c depends on the polylog exponent d only; reason: as in the published Theorem 1.1: the proof in §5 feeds the assumed algorithm instances whose log u depends on the parameters, so the Ω-constant depends on the O(1) exponent
--   - encoding: (log u)^{O(1)} → log(u+2)^d; reason: log u is 0 at u = 1, where a machine needs at least one step; the two agree up to constants for u ≥ 2
--   - reading: "can be solved in time" on the integer side, "by a randomized algorithm" only on the real side → a deterministic hypothesis (a run on the all-false coin tape), one program for all n and u, word bound ((n+2)(u+2))^c; reason: the wording marks only the conclusion as randomized, as in the published Theorem 1.1; words of O(log n + log u) bits hold the weights
--   - reading: randomized algorithm correct with high probability (p.9) → for every failure exponent a a program, worst-case time κ·n^{3−cε²} on every coin tape, success probability ≥ 1 − n^{−a}; reason: the paper's definition of high probability, p.9, with the failure exponent arbitrarily large; the page bounds the running time without an expectation
--   - encoding: three n × n matrices as mathematical objects → fixed cell layouts (n, u, presence flags, values) of the published RealAPSP.Triangles, and n ≥ 1; reason: a machine statement needs a layout; O(·) bounds are 0 at n = 0, where the instance is empty
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Theorem 1.3, p.2 (PDF p.4); proof §5, pp.16–21 (PDF pp.18–23)

import Mathlib
import Definitions.Def_RealAPSP_Supplement_ExactTriangle

namespace RealAPSP

namespace Supplement

/-- **Theorem 1.3 (Real-to-Integer Reduction for Exact Triangle).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.2 (PDF p.4); proved in §5, pp.16–21 (PDF pp.18–23).

For every polylog exponent `d` there is `c > 0` such that for every `ε > 0`: if Integer Exact Triangle with weights from `{−u, …, u}` (⊥ allowed) is decided
deterministically in time `O(n^{3−ε} (log(u+2))^d)`, then Real Exact Triangle (⊥ allowed) is decided in time `O(n^{3−cε²})` by a randomized algorithm correct with
high probability.

**Formalization Note.** The machine, word bounds and the time and success forms are those of the published `RealAPSP.Machine` and `RealAPSP.Problems`, through
`IntExactTriDecided` and `RealExactTriSolved`. The saving `c` depends on `d` only and is chosen before `ε`, and before the failure exponent inside
`RealExactTriSolved`, exactly as in the published `RealAPSP.theorem_1_1`. -/
theorem theorem_1_3 :
    ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → IntExactTriDecided ε d → RealExactTriSolved (3 - c * ε ^ 2) := by sorry

end Supplement

end RealAPSP
