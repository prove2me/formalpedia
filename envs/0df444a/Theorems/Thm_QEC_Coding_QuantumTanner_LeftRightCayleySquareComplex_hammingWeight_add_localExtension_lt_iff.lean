-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_hammingWeight_add_localExtension_lt_iff
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.hammingWeight_add_localExtension_lt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:27.287921+00:00
-- url     : https://prove2.me/theorems/ed6d2379-abbe-4580-8a2e-b40aab5db89c
-- title:
--   Left Right Cayley Square Complex: hamming Weight add local Extension lt iff
-- statement:
--   A locally weight-reducing tensor check really reduces the global word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L108-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L108-L115

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.hammingWeight_add_localExtension_lt_iff
    (X : LeftRightCayleySquareComplex G A B Square) (vertex : G × Bool)
    (x : Word (ZMod 2) Square) (c : Word (ZMod 2) (A × B)) :
    HammingWeight (x + X.localExtension vertex c) < HammingWeight x ↔
      HammingWeight (X.localRestriction vertex x + c) <
        HammingWeight (X.localRestriction vertex x) := by sorry
