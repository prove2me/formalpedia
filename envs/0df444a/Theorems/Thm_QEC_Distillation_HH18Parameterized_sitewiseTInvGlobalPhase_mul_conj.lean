-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_sitewiseTInvGlobalPhase_mul_conj
-- name    : QEC.Distillation.HH18Parameterized.sitewiseTInvGlobalPhase_mul_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:56:57.996205+00:00
-- url     : https://prove2.me/theorems/c882c0f0-6330-40a0-9e7c-640bbdd252b9
-- title:
--   HH18 Parameterized: sitewise TInv Global Phase mul conj
-- statement:
--   The explicit finite product scalar has unit modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L287-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L287-L297

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.sitewiseTInvGlobalPhase_mul_conj {m w : Nat}
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    sitewiseTInvGlobalPhase error outcomes *
      star (sitewiseTInvGlobalPhase error outcomes) = 1 := by sorry
