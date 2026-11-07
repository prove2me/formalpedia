-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_hammingWeight_partition_link
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.hammingWeight_partition_link
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:05.303867+00:00
-- url     : https://prove2.me/theorems/f7116233-c820-43cb-8d29-ca731f4d4ab9
-- title:
--   Left Right Cayley Square Complex: hamming Weight partition link
-- statement:
--   Partition global weight into the link weight and the unchanged exterior.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L72-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L72-L81

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.hammingWeight_partition_link
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) :
    HammingWeight x = HammingWeight (X.localRestriction vertex x) +
      (hammingSupport x \ Finset.univ.image (X.link vertex)).card := by sorry
