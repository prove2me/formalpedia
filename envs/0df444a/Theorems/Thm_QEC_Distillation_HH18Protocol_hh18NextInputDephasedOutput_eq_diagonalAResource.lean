-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_hh18NextInputDephasedOutput_eq_diagonalAResource
-- name    : QEC.Distillation.HH18Protocol.hh18NextInputDephasedOutput_eq_diagonalAResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:03:27.898196+00:00
-- url     : https://prove2.me/theorems/86d18479-5674-47a3-8384-7c19831095b8
-- title:
--   HH18 Protocol: hh18 Next Input Dephased Output eq diagonal AResource
-- statement:
--   The HH18 Protocol construction uses the hh18 Next Input Dephased Output eq diagonal AResource property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/OutputHandoff.lean#L565-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/OutputHandoff.lean#L565-L571

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable

theorem QEC.Distillation.HH18Protocol.hh18NextInputDephasedOutput_eq_diagonalAResource
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18NextInputDephasedOutput epsilon =
      diagonalAResource (hh18NextInputRawParameter epsilon) := by sorry
