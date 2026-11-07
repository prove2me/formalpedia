-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_columnRestriction_localRestriction_rebase_right
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.columnRestriction_localRestriction_rebase_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:24:30.193508+00:00
-- url     : https://prove2.me/theorems/945b867a-c5ec-4409-a257-c49b5599fbd3
-- title:
--   Left Right Cayley Square Complex: column Restriction local Restriction rebase right
-- statement:
--   A right edge similarly transports an entire column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleyLink.lean#L38-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleyLink.lean#L38-L45

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.columnRestriction_localRestriction_rebase_right
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (b : B) :
    columnRestriction b (X.localRestriction (g, side) x) =
      columnRestriction (X.rightInverse b)
        (X.localRestriction (g * X.rightGenerator b, !side) x) := by sorry
