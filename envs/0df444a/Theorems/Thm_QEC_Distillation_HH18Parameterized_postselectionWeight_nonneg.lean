-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionWeight_nonneg
-- name    : QEC.Distillation.HH18Parameterized.postselectionWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:59:02.231937+00:00
-- url     : https://prove2.me/theorems/ff8a3eef-52f0-4044-ac7d-258031a67525
-- title:
--   HH18 Parameterized: postselection Weight nonneg
-- statement:
--   Every coarse Born weight is nonnegative because it is derived from a
--   positive physical Kraus branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L86-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L86-L89

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
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

theorem QEC.Distillation.HH18Parameterized.postselectionWeight_nonneg {w r m : Nat} (h : Admissible w r m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    0 ≤ postselectionWeight h outcome rho := by sorry
