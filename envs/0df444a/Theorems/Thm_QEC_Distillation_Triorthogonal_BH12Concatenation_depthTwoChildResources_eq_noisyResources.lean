-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoChildResources_eq_noisyResources
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildResources_eq_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:27:03.720073+00:00
-- url     : https://prove2.me/theorems/bfe160c3-6b3e-4f9d-81c4-d3b0e15fa90b
-- title:
--   BH12 Concatenation: depth Two Child Resources eq noisy Resources
-- statement:
--   The physical child resources are exactly the ordinary BH12 noisy-resource
--   family at the selected parent's derived decoded-marginal parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1363-L1372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1363-L1372

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildResources_eq_noisyResources (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    depthTwoChildResources q p port =
      noisyResources q (bh12DecodedMarginalErrorParameter q p hsuccess port) := by sorry
