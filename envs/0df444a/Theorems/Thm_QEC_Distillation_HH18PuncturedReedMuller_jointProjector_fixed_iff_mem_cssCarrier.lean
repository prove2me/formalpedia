-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_jointProjector_fixed_iff_mem_cssCarrier
-- name    : QEC.Distillation.HH18PuncturedReedMuller.jointProjector_fixed_iff_mem_cssCarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:28:16.666322+00:00
-- url     : https://prove2.me/theorems/e38a9607-1446-492a-a9e2-254e3b5e5951
-- title:
--   HH18 Punctured Reed Muller: joint Projector fixed iff mem css Carrier
-- statement:
--   The all-positive joint projector fixes exactly the actual HH18 CSS carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L394-L408
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L394-L408

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PuncturedReedMuller
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18PuncturedReedMuller.jointProjector_fixed_iff_mem_cssCarrier {w r m : Nat}
    (h : Admissible w r m)
    (psi : Qubit.QubitRegister (PhysicalSite m w)) :
    jointProjector h psi = psi ↔
      psi ∈ (cssCode h).stabilizer.code.carrier := by sorry
