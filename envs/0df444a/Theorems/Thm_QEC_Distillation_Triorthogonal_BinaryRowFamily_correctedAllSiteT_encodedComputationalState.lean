-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_encodedComputationalState
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_encodedComputationalState
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:40:06.90932+00:00
-- url     : https://prove2.me/theorems/3e757380-ce94-458c-a2e3-c586a34cd23b
-- title:
--   Binary Row Family: corrected All Site T encoded Computational State
-- statement:
--   Every encoded computational basis state has the matching corrected `T` eigenphase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2652-L2693
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2652-L2693

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_encodedComputationalState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) :
    R.correctedAllSiteT
        (R.encodedComputationalState hR label : Qubit.QubitRegister Col) =
      OneQubitMagic.phaseAmplitude
          (Real.pi / 4 *
            (HammingWeight (bitstringWordEquiv OddRow label) : Real)) •
        (R.encodedComputationalState hR label : Qubit.QubitRegister Col) := by sorry
