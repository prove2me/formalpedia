-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_deterministic_product_value_program
-- name    : QuantumMaxCutEnergy.agm_deterministic_product_value_program
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-01T15:00:57.821723+00:00
-- url     : https://prove2.me/theorems/8462331b-7265-4abd-937a-bd8ab0ac926b
-- title:
--   Deterministic finite-bit product-value program for the AGM reduction
-- statement:
--   There exists one deterministic nonnegative rational function p on all campaign inputs, with an explicit finite Boolean-machine polynomial-time program in the fixed graph encoding. For every G, p(G)≤OPT(G) and p(G)≥0.953(OPT(G)+W(G))/3. A scaled lower approximation to the classical Max-Cut SDP value is the intended numerical construction. The coefficient leaves slack for the analytic gap and certified numerical precision. The statement requires an actual encoded program and its proof; it assumes no completed SDP solver.
-- source:
--   Anshu, Gosset and Morenz, TQC2020, Theorem1 and Eqs18–19, weighted extension in proof of Theorem3, https://doi.org/10.4230/LIPIcs.TQC.2020.7 ; Briët, de Oliveira Filho and Vallentin, Theory of Computing2014, https://doi.org/10.4086/toc.2014.v010a004 . Numerical-value adaptation: use the integrality gap to scale an approximate SDP value. The finite-bit program, analytic gap and precision certificate remain open obligations.

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm_deterministic_product_value_program :
    ∃ p : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (OAI.MetricKMedian.Binary.PolyProgram
        QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
        (fun request : QuantumMaxCutEnergy.Input × List Bool => (p request.1 : ℚ))) ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (p G : ℝ) ≤ QuantumMaxCutEnergy.optimum G ∧
        (0.953 : ℝ) * (QuantumMaxCutEnergy.optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤
          (p G : ℝ) := by sorry
