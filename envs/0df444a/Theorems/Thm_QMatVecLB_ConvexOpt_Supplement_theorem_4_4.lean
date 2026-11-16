-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_Supplement_theorem_4_4
-- name    : QMatVecLB.ConvexOpt.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:23:47.870336+00:00
-- url     : https://prove2.me/theorems/fb5cbf99-6113-41e9-8bf7-c1665a2a7c4a
-- title:
--   Theorem 4.4 — trace lower bound
-- statement:
--   There are a constant $c>0$ and an $N\ge2$ such that, for every $n\ge N$, the following holds. Consider any quantum algorithm in the matrix-vector query model that makes $t$ queries to the phase oracle $\hat U_A|x,y\rangle=e^{2\pi i\,y^{\mathsf T}Ax}|x,y\rangle$ on grid vectors $x,y\in D_k^n$ (any discretization level $k\ge1$, any finite workspace) and outputs a real number. If, for every real $n\times n$ matrix $A$ whose entries satisfy
--   $$|A_{ij}|\le24n^{3/2}\quad\text{for all }i,j,$$
--   the output $y$ satisfies $|y-\operatorname{tr}A|<\frac13$ with probability at least $\frac23$, then
--   $$t\ \ge\ c\,\frac{n}{\log n}.$$
--
--   So computing the trace to additive error less than $1/3$ with bounded error needs $\Omega(n/\log n)$ matrix-vector queries, even under the entry promise. It is a companion result of the paper and is not used in the proof of the mission's goal.
--
--   Differences from the source:
--   - encoding: t-query quantum algorithms in the matrix-vector query model with the phase oracle on the grid D_k^n → QueryAlg (MatQuery n k) W Y t from the published QueryCircuit/GridOracle definitions: t+1 input-independent unitaries, exact diagonal phase e^{2πi yᵀAx} on grid vectors, arbitrary finite workspace W, Born-rule probabilities and a basis-output map, quantified over every k ≥ 1; reason: this is the query model of Sections 2–3 as already published in the base mission; arbitrary final measurements are represented by unitary dilation into the unrestricted workspace
--   - encoding: bounded-error query complexity Ω(n/log n) → there is c > 0 (and an N ≥ 2 for the n/log n bounds) such that for every n in range, every k ≥ 1, finite W and t-query algorithm whose success probability is ≥ 2/3 on every promised input has t ≥ c·n/log n (resp. c·n); reason: expands the Ω and bounded-error conventions of Section 2; the constant c precedes n, and raising an eventual threshold to N ≥ 2 (so that log n > 0) loses no instance
--   - encoding: computing the trace with additive error less than 1/3 → the output y ∈ ℝ satisfies |y − tr A| < 1/3 (strict) with probability ≥ 2/3; reason: the page's strict inequality and the bounded-error convention
--   - encoding: entries at most 24n^{3/2} in magnitude → ∀ i j, |A i j| ≤ 24·n^{3/2} (rpow); reason: "at most" is non-strict; the promise is on entries
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Theorem 4.4, PDF p. 11 (printed p. 10).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Supplement_Witness

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt.Supplement
attribute [local instance] Classical.propDecidable

theorem theorem_4_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ k : ℕ, 1 ≤ k → ∀ (W : Type) [Fintype W] (t : ℕ)
        (alg : QueryAlg (MatQuery n k) W ℝ t),
      (∀ A : RMat n, (∀ i j, |A i j| ≤ 24 * (n : ℝ) ^ ((3 : ℝ) / 2)) →
        (2/3 : ℝ) ≤ alg.prob (matPhase A) (fun y => |y - A.trace| < 1 / 3)) →
      c * (n : ℝ) / Real.log n ≤ (t : ℝ) := by sorry

end QMatVecLB.ConvexOpt.Supplement
