-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_prepareMeasuredResources_noisyResources_toOperator
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.prepareMeasuredResources_noisyResources_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:44:17.222296+00:00
-- url     : https://prove2.me/theorems/7d1fe004-aa0f-4cb9-a8ac-02f517ba74e3
-- title:
--   BH12 Protocol: prepare Measured Resources noisy Resources to Operator
-- statement:
--   The BH12 Protocol construction uses the prepare Measured Resources noisy Resources to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1469-L1478
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1469-L1478

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.prepareMeasuredResources_noisyResources_toOperator (q : Nat)
    (p : ErrorParameter) :
    (prepareMeasuredResources q (noisyResources q p)).toOperator =
      ∑ error : PhysicalError q,
        (errorWordProbability p error : Complex) •
          (errorWordBasisDensity error).toOperator := by sorry
