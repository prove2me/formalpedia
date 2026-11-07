-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_support_sdiff_link_add_localExtension
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.support_sdiff_link_add_localExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:01.106204+00:00
-- url     : https://prove2.me/theorems/1de0f3a3-c0e1-41a0-b4aa-4c0dae7e3e4e
-- title:
--   Left Right Cayley Square Complex: support sdiff link add local Extension
-- statement:
--   Adding an extended local word changes no exterior coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L84-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L84-L92

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.support_sdiff_link_add_localExtension
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) (c : Word (ZMod 2) (A × B)) :
    hammingSupport (x + X.localExtension vertex c) \ Finset.univ.image (X.link vertex) =
      hammingSupport x \ Finset.univ.image (X.link vertex) := by sorry
