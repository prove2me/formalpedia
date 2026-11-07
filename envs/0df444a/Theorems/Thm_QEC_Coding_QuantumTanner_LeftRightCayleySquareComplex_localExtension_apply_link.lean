-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:14:54.957201+00:00
-- url     : https://prove2.me/theorems/f7454e27-554f-4172-b4ee-117a307c8ad1
-- title:
--   Left Right Cayley Square Complex: local Extension apply link
-- statement:
--   The Left Right Cayley Square Complex construction uses the local Extension apply link property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L36-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L36-L39

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (c : Word (ZMod 2) (A × B)) (ab : A × B) :
    X.localExtension vertex c (X.link vertex ab) = c ab := by sorry
