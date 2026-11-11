-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_tripleOverlap_cast
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.tripleOverlap_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:26:35.387361+00:00
-- url     : https://prove2.me/theorems/c635a525-1332-42e9-a408-f8f704372d5e
-- title:
--   Binary Row Family: triple Overlap cast
-- statement:
--   Casting an exact triple-overlap count gives its cubic `F₂` sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L210-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L210-L213

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.tripleOverlap_cast (x y z : Word (ZMod 2) Col) :
    (tripleOverlap x y z : ZMod 2) = ∑ j, x j * y j * z j := by sorry
