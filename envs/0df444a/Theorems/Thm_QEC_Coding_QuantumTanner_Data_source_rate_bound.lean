-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_source_rate_bound
-- name    : QEC.Coding.QuantumTanner.Data.source_rate_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:00:13.157185+00:00
-- url     : https://prove2.me/theorems/26d95bdd-5274-46b8-b08a-60aa0d2e141a
-- title:
--   Data: source rate bound
-- statement:
--   Complementary local-code dimensions and the actual number of squares
--   give the source rate bound. The real row rate need only be bounded above by
--   `rho`; flooring the row count therefore does not weaken the bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Parameters.lean#L75-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Parameters.lean#L75-L110

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.Data
open Classical
universe v
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.source_rate_bound
    (D : Data G A B Square XBasis ZBasis) (Delta r : Nat) (rho : ℝ)
    (hDelta : 0 < Delta) (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r ≤ Delta) (hRho : 0 ≤ rho) (hRhoHalf : rho < 1 / 2)
    (hRate : (r : ℝ) ≤ rho * Delta)
    (hCodeA : Dimension D.codeA = r) (hCodeB : Dimension D.codeB = Delta - r) :
    (1 - 2 * rho) ^ 2 * D.blockLength ≤ (D.encodedDimension : ℝ) := by sorry
