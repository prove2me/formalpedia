-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_inner_self
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_inner_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:12:52.327256+00:00
-- url     : https://prove2.me/theorems/a6ac4566-1585-45ac-953a-9856c5a761d4
-- title:
--   Binary Row Family: logical Magic State inner self
-- statement:
--   The declared logical magic state has unit norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1195-L1241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1195-L1241

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
open QEC.Distillation.Triorthogonal.BinaryRowFamily
attribute [-instance] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_inner_self
    (Index : Type u) [Fintype Index] [DecidableEq Index] :
    @inner Complex (Qubit.QubitRegister Index)
        (PiLp.innerProductSpace fun _ : Qubit.Bitstring Index => Complex).toInner
        (logicalMagicState Index) (logicalMagicState Index) = 1 := by sorry
