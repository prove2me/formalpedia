-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12AcceptedOutput_eq_resourceAcceptedOutput
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12AcceptedOutput_eq_resourceAcceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:30:37.405857+00:00
-- url     : https://prove2.me/theorems/52d926b6-aaf1-4031-8f66-42d92e0fc22c
-- title:
--   BH12 Concatenation: bh12 Accepted Output eq resource Accepted Output
-- statement:
--   At positive raw success mass, the accepted output is the actual normalized
--   accepted endpoint of #755's resource-dependent run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L346-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L346-L358

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceAcceptedWeight_noisyResources_eq_rawSuccessMass

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12AcceptedOutput_eq_resourceAcceptedOutput (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) :
    bh12AcceptedOutput q p =
      resourceAcceptedOutput q (noisyResources q p)
        (by
          rw [resourceAcceptedWeight_noisyResources_eq_rawSuccessMass]
          exact hsuccess) := by sorry
