-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_localExtension_mem_middleBoundaryCode
-- name    : QEC.Coding.QuantumTanner.Data.localExtension_mem_middleBoundaryCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:28.731729+00:00
-- url     : https://prove2.me/theorems/b32e6ee2-b138-44a2-966b-e860592dac90
-- title:
--   Data: local Extension mem middle Boundary Code
-- statement:
--   A primal tensor word extends into the actual Z-check subcode.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L281-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L281-L286

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.localExtension_mem_middleBoundaryCode
    (D : Data G A B Square XBasis ZBasis) (g : G)
    (c : Word (ZMod 2) (A × B))
    (hc : c ∈ (tensorCode D.codeA D.codeB).carrier) :
    D.complex.localExtension (g, false) c ∈ D.chainComplex.middleBoundaryCode.carrier := by sorry
