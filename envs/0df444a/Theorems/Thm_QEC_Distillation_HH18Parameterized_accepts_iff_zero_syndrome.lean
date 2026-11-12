-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_accepts_iff_zero_syndrome
-- name    : QEC.Distillation.HH18Parameterized.accepts_iff_zero_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:42:47.664681+00:00
-- url     : https://prove2.me/theorems/c9159d2f-7316-46ca-ab82-54cb04eed59e
-- title:
--   HH18 Parameterized: accepts iff zero syndrome
-- statement:
--   All-positive visible outcomes are exactly a zero symplectic syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L61-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L61-L92

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

theorem QEC.Distillation.HH18Parameterized.accepts_iff_zero_syndrome (w r m : Nat) (error : PhysicalErrorWord m w) :
    Accepts w r m error ↔
      stabilizerSyndrome
        (HH18PuncturedReedMuller.checkGenerator w r m)
        (errorPauli error) = 0 := by sorry
