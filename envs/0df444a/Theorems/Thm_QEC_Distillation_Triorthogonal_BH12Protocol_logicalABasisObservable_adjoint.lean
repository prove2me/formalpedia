-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisObservable_adjoint
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisObservable_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:08:24.057878+00:00
-- url     : https://prove2.me/theorems/b450d14c-3dd3-4c82-9d90-de2753abe30f
-- title:
--   BH12 Protocol: logical ABasis Observable adjoint
-- statement:
--   The BH12 Protocol construction uses the logical ABasis Observable adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2645-L2649
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2645-L2649

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisObservable_adjoint {q : Nat} (a : OddRow q) :
    LinearMap.adjoint (logicalABasisObservable a) =
      logicalABasisObservable a := by sorry
