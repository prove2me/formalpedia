-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawSyndromeBranch_eq
-- name    : QEC.Distillation.HH18Parameterized.rawSyndromeBranch_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:41:01.831647+00:00
-- url     : https://prove2.me/theorems/90f48259-a263-4116-a199-fc2b8920ee71
-- title:
--   HH18 Parameterized: raw Syndrome Branch eq
-- statement:
--   The full instrument selects precisely the syndrome derived from the
--   physical Pauli-error word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L315-L341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L315-L341

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18Parameterized.rawSyndromeBranch_eq {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w)
    (syndrome : Syndrome w r m) :
    rawSyndromeBranch h error outcomes syndrome =
      if syndrome = measuredSyndrome w r m error then
        errorBranchOperator h hdegree error
      else
        0 := by sorry
