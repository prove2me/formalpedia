-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12SelectedPortDensity_eq_resourceAcceptedMarginal
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12SelectedPortDensity_eq_resourceAcceptedMarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:35:13.726241+00:00
-- url     : https://prove2.me/theorems/a6e4bdd6-a2bb-4251-a29e-c426f8a66815
-- title:
--   BH12 Concatenation: bh12 Selected Port Density eq resource Accepted Marginal
-- statement:
--   At positive raw success mass, the selected-port density is the partial
--   trace of the actual normalized resource-accepted output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1227-L1235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1227-L1235

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12SelectedPortDensity_eq_resourceAcceptedMarginal (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    bh12SelectedPortDensity q p port =
      (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        (resourceAcceptedOutput q (noisyResources q p)
          (by
            rw [resourceAcceptedWeight_noisyResources_eq_rawSuccessMass]
            exact hsuccess)) := by sorry
