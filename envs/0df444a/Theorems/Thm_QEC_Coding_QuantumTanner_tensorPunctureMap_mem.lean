-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_tensorPunctureMap_mem
-- name    : QEC.Coding.QuantumTanner.tensorPunctureMap_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:51:25.742834+00:00
-- url     : https://prove2.me/theorems/14ddd838-3863-44e5-baa0-c3be7bb084a1
-- title:
--   Quantum Tanner: tensor Puncture Map mem
-- statement:
--   Rectangular puncturing sends original tensor words to punctured tensor words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L48-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L48-L60

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.tensorPunctureMap_mem
    (CA : LinearCode F A) (CB : LinearCode F B)
    (removedA : Finset A) (removedB : Finset B)
    (x : Word F (A × B)) (hx : x ∈ (tensorCode CA CB).carrier) :
    tensorPunctureMap removedA removedB x ∈
      (tensorCode (puncturedCode CA removedA) (puncturedCode CB removedB)).carrier := by sorry
