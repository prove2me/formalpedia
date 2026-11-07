-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_rowRestriction_localRestriction_rebase_left
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.rowRestriction_localRestriction_rebase_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:24:05.848664+00:00
-- url     : https://prove2.me/theorems/24b312ec-d383-40f9-8257-10528662f13b
-- title:
--   Left Right Cayley Square Complex: row Restriction local Restriction rebase left
-- statement:
--   A left edge transports an entire row without changing its word coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleyLink.lean#L28-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleyLink.lean#L28-L35

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.rowRestriction_localRestriction_rebase_left
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) :
    rowRestriction a (X.localRestriction (g, side) x) =
      rowRestriction (X.leftInverse a)
        (X.localRestriction (X.leftGenerator a * g, !side) x) := by sorry
