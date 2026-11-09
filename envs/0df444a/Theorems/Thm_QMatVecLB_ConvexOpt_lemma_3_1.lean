-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_3_1
-- name    : QMatVecLB.ConvexOpt.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:08:36.171358+00:00
-- url     : https://prove2.me/theorems/f1da005b-36b2-4a8e-b1d5-183cf71df824
-- title:
--   Lemma 3.1 — Fourier support of query probabilities
-- statement:
--   Let $n$ be the matrix dimension, $k\ge1$ the freely chosen discretization level, and $t$ the number of queries. For every finite workspace, normalized initial state, input-independent gates, output map and output event $S$, there is a finitely supported complex measure $\mu$, independent of the input matrix $A$, such that
--
--   $$\Pr_A[S]=\sum_M\mu(M)e^{2\pi i\langle A,M\rangle},\qquad \operatorname{supp}(\mu)\subseteq\{M:\operatorname{rank}M\le2t\}.$$
--
--   The same measure works for every real input matrix. This is the rank constraint on the Fourier representation of an algorithm's measurement probabilities.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: finite-register t-query quantum algorithms and general final measurements → normalized finite-dimensional complex states, t+1 input-independent unitary gates, exact diagonal phase queries tensored with an arbitrary finite workspace, and basis readout with an output map; reason: this is the circuit model of Section 3.1; arbitrary finite outcome measurements are represented by unitary dilation into the unrestricted workspace
--   - encoding: a discrete complex measure on the rank variety → a finitely supported coefficient function on matrices, zero outside rank at most 2t; reason: the source explicitly states that these integrals are finite sums
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 3.1, PDF p. 6 (printed p. 5).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_GridOracle

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_3_1 (n k t : ℕ) (hk : 1 ≤ k)
    (W Y : Type) [Fintype W] (alg : QueryAlg (MatQuery n k) W Y t) (S : Y → Prop) :
    ∃ μ : RMat n →₀ ℂ,
      (∀ M ∈ μ.support, M ∈ rankVariety n (2*t)) ∧
      ∀ A : RMat n,
        (alg.prob (matPhase A) S : ℂ) =
          ∑ M ∈ μ.support, μ M * phaseExp (matrixPair A M) := by sorry

end QMatVecLB.ConvexOpt
