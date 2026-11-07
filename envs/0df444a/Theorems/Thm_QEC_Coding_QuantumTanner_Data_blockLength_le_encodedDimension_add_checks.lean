-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_le_encodedDimension_add_checks
-- name    : QEC.Coding.QuantumTanner.Data.blockLength_le_encodedDimension_add_checks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:59:55.963216+00:00
-- url     : https://prove2.me/theorems/4223076d-6f8c-4893-af7b-2989e874c558
-- title:
--   Data: block Length le encoded Dimension add checks
-- statement:
--   Rank-nullity bounds the number of encoded qubits using the actual
--   numbers of chosen local checks, even if those checks are dependent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Parameters.lean#L28-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Parameters.lean#L28-L45

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

theorem QEC.Coding.QuantumTanner.Data.blockLength_le_encodedDimension_add_checks
    (D : Data G A B Square XBasis ZBasis) :
    D.blockLength ≤ D.encodedDimension +
      Fintype.card G * (Fintype.card XBasis + Fintype.card ZBasis) := by sorry
