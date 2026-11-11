-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply_of_reducedCombination
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply_of_reducedCombination
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:38:20.709304+00:00
-- url     : https://prove2.me/theorems/ad5deab6-4aaf-4eda-9258-eb33a192010b
-- title:
--   Binary Row Family: corrected All Site T apply of reduced Combination
-- statement:
--   On every reduced-row combination, corrected transversal `T` leaves exactly
--   the odd-row logical phase exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2444-L2462
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2444-L2462

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply_of_reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister Col) (bits : Qubit.Bitstring Col)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (hbits : bitstringWordEquiv Col bits = R.reducedCombination c) :
    R.correctedAllSiteT psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi / 4 *
          ((R.logicalExponent8 c R.reducedRowIndexList).val : Real)) *
        psi bits := by sorry
