-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_composeAtoms_apply
-- name    : QEC.Distillation.Triorthogonal.composeAtoms_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:35:05.506197+00:00
-- url     : https://prove2.me/theorems/04a24e9b-758c-4d77-8db8-bc15f1bc699c
-- title:
--   Triorthogonal: compose Atoms apply
-- statement:
--   The Triorthogonal construction uses the compose Atoms apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L829-L841
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L829-L841

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]

theorem QEC.Distillation.Triorthogonal.composeAtoms_apply (atoms : List (CliffordCorrectionAtom Index))
    (psi : Qubit.QubitRegister Index) (bits : Qubit.Bitstring Index) :
    UnitaryTransport.composeList (atoms.map CliffordCorrectionAtom.realized) psi bits =
      OneQubitMagic.phaseAmplitude (atomAngleSum atoms bits) * psi bits := by sorry
