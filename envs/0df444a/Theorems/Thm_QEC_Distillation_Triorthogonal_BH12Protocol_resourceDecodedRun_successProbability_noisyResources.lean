-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceDecodedRun_successProbability_noisyResources
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_successProbability_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:05:15.307141+00:00
-- url     : https://prove2.me/theorems/0005cefc-909c-460c-bcc4-9ee60912ce34
-- title:
--   BH12 Protocol: resource Decoded Run success Probability noisy Resources
-- statement:
--   On the diagonal BH12 resource family, the generic run recovers the
--   previously derived physical raw success mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1854-L1858
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1854-L1858

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_successProbability_noisyResources (q : Nat)
    (p : ErrorParameter) :
    (resourceDecodedRun q (noisyResources q p)).successProbability =
      rawSuccessMass q p := by sorry
