-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_intertwines_logicalComputationalState
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_intertwines_logicalComputationalState
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:40:07.114294+00:00
-- url     : https://prove2.me/theorems/ee9d2f90-c970-445f-a8f9-6c676a8adc57
-- title:
--   Binary Row Family: corrected All Site T intertwines logical Computational State
-- statement:
--   Corrected physical `T` intertwines encoding on every computational basis state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2696-L2709
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2696-L2709

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
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_intertwines_logicalComputationalState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) :
    R.correctedAllSiteT
        (R.encoding hR (logicalComputationalState label) : Qubit.QubitRegister Col) =
      (R.encoding hR
        ((allSiteT (Index := OddRow)) (logicalComputationalState label)) :
          Qubit.QubitRegister Col) := by sorry
