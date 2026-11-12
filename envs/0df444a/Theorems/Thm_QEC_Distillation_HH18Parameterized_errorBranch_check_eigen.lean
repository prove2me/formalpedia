-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranch_check_eigen
-- name    : QEC.Distillation.HH18Parameterized.errorBranch_check_eigen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:57:59.963191+00:00
-- url     : https://prove2.me/theorems/9bd46629-ce16-4c63-8e87-b18cbd3c1fe3
-- title:
--   HH18 Parameterized: error Branch check eigen
-- statement:
--   The actual Pauli-error branch has exactly its derived signed check
--   eigenvalues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L184-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L184-L246

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
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

theorem QEC.Distillation.HH18Parameterized.errorBranch_check_eigen {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (check : CheckIndex w r m) :
    toHermitianQubitOperator
        (HH18PuncturedReedMuller.checkGenerator w r m check)
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree)) =
      (measuredSyndrome w r m error check).sign •
        HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree) := by sorry
