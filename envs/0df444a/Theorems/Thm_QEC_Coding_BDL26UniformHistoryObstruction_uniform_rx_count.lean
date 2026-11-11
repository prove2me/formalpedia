-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_uniform_rx_count
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.uniform_rx_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:33:53.007351+00:00
-- url     : https://prove2.me/theorems/473e8528-57c4-4a39-adb5-f3749c8e1099
-- title:
--   BDL26 Uniform History Obstruction: uniform rx count
-- statement:
--   Exact number of RX steps in the physical-C2 suffix of this even-depth input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L128-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L128-L128

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.uniform_rx_count (j : Nat) : ((2 * j + 2) + 1) / 2 = j + 1 := by sorry
