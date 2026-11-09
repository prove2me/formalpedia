-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_3_3
-- name    : QMatVecLB.ConvexOpt.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:35.510518+00:00
-- url     : https://prove2.me/theorems/aacf0b12-9609-431e-9d32-af34e1b1f6f8
-- title:
--   Lemma 3.3 — failure forced by a dual witness
-- statement:
--   Let $P$ be a promise set of real $n\times n$ matrices and $D$ a measurable function on the full matrix space taking values in $\{0,1\}$. Let $\xi=\xi_0+\xi_1$ be a rank-$2t$ dual witness for $P$. Every $t$-query algorithm, at any discretization level $k\ge1$ and with any finite workspace, has worst-case failure probability at least
--
--   $$b=\frac{\left|\int D(A)\,d\xi(A)\right|-\|\xi_1\|_1}{\|\xi_0\|_1}.$$
--
--   Precisely, for each real $\delta<b$, some $A\in P$ has $|D(A)-p(A)|>\delta$, where $p(A)$ is the algorithm's probability of returning true. This separates the analytic witness conditions from any particular circuit.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: finite-register t-query quantum algorithms and general final measurements → normalized finite-dimensional complex states, t+1 input-independent unitary gates, exact diagonal phase queries tensored with an arbitrary finite workspace, and basis readout with an output map; reason: this is the circuit model of Section 3.1; arbitrary finite outcome measurements are represented by unitary dilation into the unrestricted workspace
--   - encoding: two arbitrary finite complex measures → two integrable complex densities with respect to an arbitrary common finite dominating measure; reason: every such pair has this representation by taking the sum of its variation measures; no absolute continuity with respect to Lebesgue measure is imposed
--   - encoding: any extension D and the supremum of the failure probabilities over P → a measurable {0,1}-valued real extension D, and for every delta below the bound a promise input with failure greater than delta; reason: measurability is the integral convention; this is equivalent to the supremum bound because the positive witness mass forces P nonempty and failure probabilities lie in [0,1]
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 3.3, PDF p. 7 (printed p. 6).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_DualWitness

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_3_3 (n k t : ℕ) (hk : 1 ≤ k)
    (P : Set (RMat n)) (D : RMat n → ℝ) (hD : Measurable D)
    (hvalues : ∀ A, D A = 0 ∨ D A = 1)
    (ξ : WitnessMeasures n) (hξ : IsDualWitness ξ P (2*t))
    (W : Type) [Fintype W] (alg : QueryAlg (MatQuery n k) W Bool t) :
    ∀ δ : ℝ, δ < (‖ξ.integral (fun A => (D A : ℂ))‖ - ξ.mass1) / ξ.mass0 →
      ∃ A ∈ P, δ < |D A - alg.prob (matPhase A) (fun b => b = true)| := by sorry

end QMatVecLB.ConvexOpt
