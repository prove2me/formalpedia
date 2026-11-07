-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_eq_zero_of_not_incident
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_eq_zero_of_not_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:51.348126+00:00
-- url     : https://prove2.me/theorems/fceef8db-93f1-444c-a7a4-49c469703441
-- title:
--   Left Right Cayley Square Complex: local Extension eq zero of not incident
-- statement:
--   The Left Right Cayley Square Complex construction uses the local Extension eq zero of not incident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L49-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L49-L55

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_eq_zero_of_not_incident
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (c : Word (ZMod 2) (A × B)) {q : Square}
    (hq : q ∉ Finset.univ.image (X.link vertex)) :
    X.localExtension vertex c q = 0 := by sorry
