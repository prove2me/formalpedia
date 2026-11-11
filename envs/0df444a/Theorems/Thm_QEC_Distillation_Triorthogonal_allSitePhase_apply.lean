-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_allSitePhase_apply
-- name    : QEC.Distillation.Triorthogonal.allSitePhase_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:31:38.312409+00:00
-- url     : https://prove2.me/theorems/bf3e9992-eb92-44b7-b403-3b157345e571
-- title:
--   Triorthogonal: all Site Phase apply
-- statement:
--   The raw all-site phase layer contributes exactly the physical
--   Hamming-weight phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L767-L788
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L767-L788

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]

theorem QEC.Distillation.Triorthogonal.allSitePhase_apply
    (theta : Real)
    (psi : Qubit.QubitRegister Index) (bits : Qubit.Bitstring Index) :
    allSitePhase theta psi bits =
      OneQubitMagic.phaseAmplitude
        (theta *
          (HammingWeight (bitstringWordEquiv Index bits) : Real)) *
        psi bits := by sorry
