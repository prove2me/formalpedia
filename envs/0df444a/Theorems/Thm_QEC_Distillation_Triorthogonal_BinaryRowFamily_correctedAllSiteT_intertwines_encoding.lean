-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_intertwines_encoding
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_intertwines_encoding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:40:56.413366+00:00
-- url     : https://prove2.me/theorems/55a730f1-873d-4acc-bac2-0b6115146e2f
-- title:
--   Binary Row Family: corrected All Site T intertwines encoding
-- statement:
--   Corrected physical `T` intertwines the encoding on every logical state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2712-L2734
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2712-L2734

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_intertwines_encoding
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister OddRow) :
    R.correctedAllSiteT
        (R.encoding hR psi : Qubit.QubitRegister Col) =
      (R.encoding hR ((allSiteT (Index := OddRow)) psi) :
        Qubit.QubitRegister Col) := by sorry
