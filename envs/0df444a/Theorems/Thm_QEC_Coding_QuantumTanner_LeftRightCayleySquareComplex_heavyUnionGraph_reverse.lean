-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_heavyUnionGraph_reverse
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.heavyUnionGraph_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:51:38.916467+00:00
-- url     : https://prove2.me/theorems/e2c0074d-af03-4a60-b5c0-45bc4cebc955
-- title:
--   Left Right Cayley Square Complex: heavy Union Graph reverse
-- statement:
--   Reversing a realized Cayley edge preserves its shared-line weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L185-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L185-L236

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.heavyUnionGraph_reverse
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (g h : G) :
    X.heavyUnionGraph side x cutoff g h = X.heavyUnionGraph (!side) x cutoff h g := by sorry
