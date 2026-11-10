-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementSupport_rxConnectingQZ1_apply_z
-- name    : QEC.Coding.BDL26ReplacementSupport.rxConnectingQZ1_apply_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:36:28.200138+00:00
-- url     : https://prove2.me/theorems/7d9f7152-43c1-43b6-9e37-52bdf1194df8
-- title:
--   BDL26 Replacement Support: rx Connecting QZ1 apply z
-- statement:
--   The Q-to-Z matrix term is the sum of the actual two-terminal restrictions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L507-L536
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementSupport.lean#L507-L536

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26ReplacementSupport.rxConnectingQZ1_apply_z
    (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S)) (z : P.Z) (copy : Two) :
    rxConnectingQZ1 P S word (Sum.inr (z, copy)) =
      ∑ q : P.Q, rxQOutgoing P q S
        (fun vertex => word (Sum.inr ⟨q, vertex⟩)) z copy := by sorry
