-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
-- name    : QEC.Distillation.Triorthogonal.atomAngleSum_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:28:09.345535+00:00
-- url     : https://prove2.me/theorems/447c7cd4-02e6-4ff9-8674-c1611e83a23f
-- title:
--   Triorthogonal: atom Angle Sum append
-- statement:
--   The Triorthogonal construction uses the atom Angle Sum append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L824-L827
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L824-L827

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

theorem QEC.Distillation.Triorthogonal.atomAngleSum_append
    (xs ys : List (CliffordCorrectionAtom Index)) (bits : Qubit.Bitstring Index) :
    atomAngleSum (xs ++ ys) bits = atomAngleSum xs bits + atomAngleSum ys bits := by sorry
