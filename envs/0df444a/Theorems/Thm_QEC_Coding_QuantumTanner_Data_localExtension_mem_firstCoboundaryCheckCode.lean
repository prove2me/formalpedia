-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_localExtension_mem_firstCoboundaryCheckCode
-- name    : QEC.Coding.QuantumTanner.Data.localExtension_mem_firstCoboundaryCheckCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:25.782892+00:00
-- url     : https://prove2.me/theorems/ddeed1ff-11fc-4a83-a459-642cc7e36f88
-- title:
--   Data: local Extension mem first Coboundary Check Code
-- statement:
--   A dual-local-code tensor word extends into the actual X-check subcode.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L270-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L270-L278

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

theorem QEC.Coding.QuantumTanner.Data.localExtension_mem_firstCoboundaryCheckCode
    (D : Data G A B Square XBasis ZBasis) (g : G)
    (c : Word (ZMod 2) (A × B))
    (hc : c ∈ (tensorCode D.codeA.dual D.codeB.dual).carrier) :
    D.complex.localExtension (g, true) c ∈ D.chainComplex.firstCoboundaryCheckCode.carrier := by sorry
