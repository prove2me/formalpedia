-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_RawData_localExtension_mem_range_zGeneratorMap
-- name    : QEC.Coding.QuantumTanner.RawData.localExtension_mem_range_zGeneratorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:07.744738+00:00
-- url     : https://prove2.me/theorems/0d350f1c-c073-4850-8f7b-8d401300f49d
-- title:
--   Raw Data: local Extension mem range z Generator Map
-- statement:
--   The primal tensor code analog gives a genuine Z check.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L246-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L246-L259

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
open QEC.Coding.QuantumTanner.RawData
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.RawData.localExtension_mem_range_zGeneratorMap
    (D : RawData G A B Square XBasis ZBasis) (g : G)
    (c : Word (ZMod 2) (A × B))
    (hc : c ∈ (tensorCode D.codeA D.codeB).carrier) :
    D.complex.localExtension (g, false) c ∈ LinearMap.range D.zGeneratorMap := by sorry
