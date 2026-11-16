-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_Supplement_theorem_5_2
-- name    : QMatVecLB.ConvexOpt.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:24:12.475232+00:00
-- url     : https://prove2.me/theorems/e23f3852-f58a-4c0e-ab16-8b00419c8e38
-- title:
--   Theorem 5.2 — sign of the determinant
-- statement:
--   Let $\mathbb E$ denote expectation over a random $n\times n$ matrix with independent $N(0,1)$ entries. There is a constant $c>0$ such that for every $n\ge1$ there is a finite entry bound $\Lambda$ with the following property. Consider any quantum algorithm that makes $t$ matrix-vector phase queries $\hat U_A|x,y\rangle=e^{2\pi i\,y^{\mathsf T}Ax}|x,y\rangle$ on grid vectors $x,y\in D_k^n$ (any $k\ge1$, any finite workspace) and outputs a bit. If for every real $n\times n$ matrix $A$ with
--   $$|\det A|\ \ge\ \tfrac18\,\mathbb E|\det A|\qquad\text{and}\qquad |A_{ij}|\le\Lambda\ \text{for all }i,j$$
--   the algorithm outputs the sign bit $[\det A\ge0]$ with probability at least $\frac23$, then
--   $$t\ \ge\ c\,n .$$
--
--   So deciding the sign of the determinant with bounded error needs $\Omega(n)$ matrix-vector queries, even with a finite bound on the entries. It is a companion result of the paper and is not used in the proof of the mission's goal.
--
--   Differences from the source:
--   - encoding: t-query quantum algorithms in the matrix-vector query model with the phase oracle on the grid D_k^n → QueryAlg (MatQuery n k) W Y t from the published QueryCircuit/GridOracle definitions: t+1 input-independent unitaries, exact diagonal phase e^{2πi yᵀAx} on grid vectors, arbitrary finite workspace W, Born-rule probabilities and a basis-output map, quantified over every k ≥ 1; reason: this is the query model of Sections 2–3 as already published in the base mission; arbitrary final measurements are represented by unitary dilation into the unrestricted workspace
--   - encoding: bounded-error query complexity Ω(n) → there is c > 0 such that for every n ≥ 1 there is Λ with: every k ≥ 1, finite W and t-query algorithm whose success probability is ≥ 2/3 on every promised input has c·n ≤ t; reason: expands the Ω and bounded-error conventions of Section 2; the constant c precedes n; stating it for every n ≥ 1 instead of eventually is equivalent, because for a suitable Λ the promise contains A and A with one row negated (opposite signs), a 0-query algorithm's output law does not depend on A, so it fails on one of them with probability ≥ 1/2, so t ≥ 1 and the finitely many small n are absorbed by shrinking c
--   - reading: "Deciding the sign of det A (and hence computing det A)" → the sign decision only: output Bool, correct answer decide (0 ≤ det A); reason: the parenthetical states no accuracy for computing det A, so it is a consequence remark, not a separate task; the sign decision is what the proof establishes
--   - encoding: the sign of det A → decide (0 ≤ det A), the paper's D(A) = 1_{det A ≥ 0}; reason: on the promise det A ≠ 0, so this is exactly the sign
--   - encoding: "even with some finite upper bound on the magnitudes of the entries" → ∃ Λ : ℝ, chosen after n and before k, W, t and the algorithm, with promise ∀ i j, |A i j| ≤ Λ; reason: the proof chooses Λ from n alone (Eq. (50))
--   - encoding: (1/8) E|det A| over i.i.d. N(0,1) entries → (1/8)·∫ |det X| d(GaussianMatrix.gaussianMatrix n n); reason: the Section 5 convention; the published Gaussian matrix law
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Theorem 5.2, PDF p. 12 (printed p. 11).

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_QMatVecLB_ConvexOpt_Supplement_Witness

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt.Supplement
attribute [local instance] Classical.propDecidable

theorem theorem_5_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∃ Λ : ℝ,
      ∀ k : ℕ, 1 ≤ k → ∀ (W : Type) [Fintype W] (t : ℕ)
        (alg : QueryAlg (MatQuery n k) W Bool t),
      (∀ A : RMat n,
        (1 / 8 : ℝ) * (∫ X : RMat n, |X.det| ∂GaussianMatrix.gaussianMatrix n n) ≤ |A.det| →
        (∀ i j, |A i j| ≤ Λ) →
        (2/3 : ℝ) ≤ alg.prob (matPhase A) (fun b => b = decide (0 ≤ A.det))) →
      c * (n : ℝ) ≤ (t : ℝ) := by sorry

end QMatVecLB.ConvexOpt.Supplement
