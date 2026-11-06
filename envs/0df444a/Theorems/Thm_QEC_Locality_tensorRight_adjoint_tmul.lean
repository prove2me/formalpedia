-- Prove2me | Theorems.Thm_QEC_Locality_tensorRight_adjoint_tmul
-- name    : QEC.Locality.tensorRight_adjoint_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:04.645141+00:00
-- url     : https://prove2.me/theorems/e91ace11-1754-47e5-94ae-9f941aed5c23
-- title:
--   Locality: tensor Right adjoint tmul
-- statement:
--   The Locality construction uses the tensor Right adjoint tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L39-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L39-L48

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.tensorRight_adjoint_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (k k' : K) (h : H) :
    LinearMap.adjoint (tensorRight H K k) (h ⊗ₜ[Complex] k') =
      (inner Complex k k') • h := by sorry
