-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:14:57.447598+00:00
-- url     : https://prove2.me/theorems/a5073ded-7700-4aa9-bec2-496513e0f82c
-- title:
--   Left Right Cayley Square Complex: local Restriction local Extension
-- statement:
--   The Left Right Cayley Square Complex construction uses the local Restriction local Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L42-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L42-L47

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
open QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (c : Word (ZMod 2) (A × B)) :
    X.localRestriction vertex (X.localExtension vertex c) = c := by sorry
