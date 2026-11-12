-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_registerBranchOperator_adjoint
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.registerBranchOperator_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:54:36.509201+00:00
-- url     : https://prove2.me/theorems/7305dd6d-f909-4bb9-851a-33943529a02f
-- title:
--   BH12 Noisy Injection: register Branch Operator adjoint
-- statement:
--   The BH12 Noisy Injection construction uses the register Branch Operator adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L726-L734
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L726-L734

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12NoisyInjection
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.registerBranchOperator_adjoint
    (error : Word (ZMod 2) Index) :
    LinearMap.adjoint (registerBranchOperator error) =
      (allSiteT (Index := Index)).toLinearEquiv.symm.toLinearMap.comp
        (toQubitOperator (cssZCheck error)) := by sorry
