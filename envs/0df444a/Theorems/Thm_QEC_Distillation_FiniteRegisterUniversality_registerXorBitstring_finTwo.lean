-- Prove2me | Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_registerXorBitstring_finTwo
-- name    : QEC.Distillation.FiniteRegisterUniversality.registerXorBitstring_finTwo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:24:35.657076+00:00
-- url     : https://prove2.me/theorems/6a3ee6d2-db48-4a9a-8dfb-8c0b1419e8f7
-- title:
--   Finite Register Universality: register Xor Bitstring fin Two
-- statement:
--   On a two-wire register, the basis-index permutation is exactly the XOR
--   coordinate permutation of the concrete #586 transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L293-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean#L293-L298

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteRegisterUniversality
open Semantics Semantics.Qubit
open GeneratedUniversality
open scoped Kronecker
variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]

theorem QEC.Distillation.FiniteRegisterUniversality.registerXorBitstring_finTwo (bits : Bitstring (Fin 2)) :
    registerXorBitstring (0 : Fin 2) 1 (by decide) bits =
      TwoQubit.xorBitstring bits := by sorry
