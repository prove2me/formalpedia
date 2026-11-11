-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_allSiteT_logicalComputationalState
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.allSiteT_logicalComputationalState
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:40:05.545851+00:00
-- url     : https://prove2.me/theorems/8066a940-7540-4a1b-b10d-dabb0bad018f
-- title:
--   Binary Row Family: all Site T logical Computational State
-- statement:
--   Simultaneous logical `T` acts diagonally on each computational basis state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2636-L2649
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2636-L2649

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.allSiteT_logicalComputationalState
    (label : Qubit.Bitstring OddRow) :
    (allSiteT (Index := OddRow)) (logicalComputationalState label) =
      OneQubitMagic.phaseAmplitude
          (Real.pi / 4 *
            (HammingWeight (bitstringWordEquiv OddRow label) : Real)) •
        logicalComputationalState label := by sorry
