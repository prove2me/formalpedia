-- Prove2me | Theorems.Thm_QMaxCutSDP_Rounding_theorem_1
-- name    : QMaxCutSDP.Rounding.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:11.953382+00:00
-- url     : https://prove2.me/theorems/396ec2be-201f-4ebd-ae54-4a6bbb5f1c2c
-- title:
--   Theorem 1 (Main) — Algorithm 1 achieves 0.562 of Quantum Max Cut optimum in expectation
-- statement:
--   Let $G$ be a graph with nonnegative edge weights and let $v$ be a feasible solution of the vector SDP (S) whose objective value is at least that of every feasible solution, in any finite dimension. Run Algorithm 1 with $v$. Its output energy is integrable, and for every unit quantum state $|\phi\rangle$,
--   $$\mathbb E\,\langle\phi(\theta)|H|\phi(\theta)\rangle\ge0.562\,\langle\phi|H|\phi\rangle.$$
--   Equivalently, its expected energy is at least $0.562$ times the maximum eigenvalue of $H$. This is the approximation guarantee for Quantum Max Cut.
--
--   **Formalization Note** The paper's proof establishes an expectation although its theorem sentence omits that qualifier. Optimality compares all feasible dimensions, not one artificially small dimension. Quantifying over all unit states expresses the maximum-eigenvalue comparison without a real supremum's default-value convention. The claim also asserts integrability of the random energy.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 10, Theorem 1 (Main); proof pp. 11–13

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory

namespace QMaxCutSDP.Rounding

/-- Lee, Theorem 1 (Main), p. 10, in the expectation form proved on p. 11. -/
theorem theorem_1 {n N : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (v : SDPVec n N) (hv : IsSFeasible v)
    (hopt : ∀ (N' : ℕ) (u : SDPVec n N'),
      IsSFeasible u → sObj G w u ≤ sObj G w v)
    (φ : State n) (hφ : star φ ⬝ᵥ φ = 1) :
    (∀ a : Fin 3, Integrable
      (fun r => energy G w (outState G (bits v a r) (thetaE v))) (stdGaussian N)) ∧
    (0.562 : ℝ) * energy G w φ ≤ expectedEnergy G w v := by sorry
end QMaxCutSDP.Rounding
