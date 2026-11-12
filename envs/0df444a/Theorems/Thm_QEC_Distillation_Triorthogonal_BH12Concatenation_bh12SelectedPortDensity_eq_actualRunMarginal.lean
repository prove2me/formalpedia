-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12SelectedPortDensity_eq_actualRunMarginal
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12SelectedPortDensity_eq_actualRunMarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:34:42.034464+00:00
-- url     : https://prove2.me/theorems/dd951225-52c4-4580-a84d-b086a7d23aa9
-- title:
--   BH12 Concatenation: bh12 Selected Port Density eq actual Run Marginal
-- statement:
--   The selected-port density is the literal partial trace of #755's actual
--   resource-decoded accepted run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1218-L1223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1218-L1223

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12SelectedPortDensity_eq_actualRunMarginal (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    bh12SelectedPortDensity q p port =
      (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        ((resourceDecodedRun q (noisyResources q p)).acceptedOutput) := by sorry
