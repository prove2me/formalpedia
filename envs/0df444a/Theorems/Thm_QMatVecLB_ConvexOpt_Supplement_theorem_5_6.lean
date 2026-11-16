-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_Supplement_theorem_5_6
-- name    : QMatVecLB.ConvexOpt.Supplement.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:25:00.674043+00:00
-- url     : https://prove2.me/theorems/7cef3512-8837-4f0a-a5bc-55ea17fd79a7
-- title:
--   Theorem 5.6 — magnitude of the determinant
-- statement:
--   There are a constant $c>0$ and an $N\ge2$ such that for every $n\ge N$ there are an additive error $\varepsilon_n>0$ and a finite entry bound $\Lambda$ with the following property. Consider any quantum algorithm that makes $t$ matrix-vector phase queries $\hat U_A|x,y\rangle=e^{2\pi i\,y^{\mathsf T}Ax}|x,y\rangle$ on grid vectors $x,y\in D_k^n$ (any $k\ge1$, any finite workspace) and outputs a real number. If for every real $n\times n$ matrix $A$ with $|A_{ij}|\le\Lambda$ for all $i,j$ the output $y$ satisfies
--   $$\big|\,y-|\det A|\,\big|\le\varepsilon_n$$
--   with probability at least $\frac23$, then
--   $$t\ \ge\ c\,\frac{n}{\log n}.$$
--
--   So computing $|\det A|$ to within some $n$-dependent additive error needs $\Omega(n/\log n)$ matrix-vector queries, even with a finite bound on the entries. It is a companion result of the paper and is not used in the proof of the mission's goal.
--
--   Differences from the source:
--   - encoding: t-query quantum algorithms in the matrix-vector query model with the phase oracle on the grid D_k^n → QueryAlg (MatQuery n k) W Y t from the published QueryCircuit/GridOracle definitions: t+1 input-independent unitaries, exact diagonal phase e^{2πi yᵀAx} on grid vectors, arbitrary finite workspace W, Born-rule probabilities and a basis-output map, quantified over every k ≥ 1; reason: this is the query model of Sections 2–3 as already published in the base mission; arbitrary final measurements are represented by unitary dilation into the unrestricted workspace
--   - encoding: bounded-error query complexity Ω(n/log n) → there is c > 0 (and an N ≥ 2 for the n/log n bounds) such that for every n in range, every k ≥ 1, finite W and t-query algorithm whose success probability is ≥ 2/3 on every promised input has t ≥ c·n/log n (resp. c·n); reason: expands the Ω and bounded-error conventions of Section 2; the constant c precedes n, and raising an eventual threshold to N ≥ 2 (so that log n > 0) loses no instance
--   - encoding: "to within some n-dependent additive error ε_n" → ∃ ε > 0 chosen after n and before k, W, t and the algorithm; success means |y − |det A|| ≤ ε; reason: "within" read as non-strict; ε_n depends on n only, as constructed in Eq. (84)
--   - encoding: "even with some finite upper bound on the magnitudes of the entries" → ∃ Λ : ℝ, chosen after n (and ε) and before the algorithm, with promise ∀ i j, |A i j| ≤ Λ; reason: the proof chooses Λ from n alone
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Theorem 5.6, PDF p. 15 (printed p. 14).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Supplement_Witness

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt.Supplement
attribute [local instance] Classical.propDecidable

theorem theorem_5_6 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ ε : ℝ, 0 < ε ∧ ∃ Λ : ℝ,
      ∀ k : ℕ, 1 ≤ k → ∀ (W : Type) [Fintype W] (t : ℕ)
        (alg : QueryAlg (MatQuery n k) W ℝ t),
      (∀ A : RMat n, (∀ i j, |A i j| ≤ Λ) →
        (2/3 : ℝ) ≤ alg.prob (matPhase A) (fun y => |y - abs A.det| ≤ ε)) →
      c * (n : ℝ) / Real.log n ≤ (t : ℝ) := by sorry

end QMatVecLB.ConvexOpt.Supplement
