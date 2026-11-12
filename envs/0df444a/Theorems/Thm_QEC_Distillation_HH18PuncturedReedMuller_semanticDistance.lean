-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_semanticDistance
-- name    : QEC.Distillation.HH18PuncturedReedMuller.semanticDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:39:07.125002+00:00
-- url     : https://prove2.me/theorems/666d9d37-619e-41ff-ad21-e9d00ca8c425
-- title:
--   HH18 Punctured Reed Muller: semantic Distance
-- statement:
--   The semantic distance of the actual source-valid HH18 CSS stabilizer is
--   the smaller complementary logical-sector binomial tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L307-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L307-L319

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

theorem QEC.Distillation.HH18PuncturedReedMuller.semanticDistance {w r m : Nat} (h : Admissible w r m) :
    StabilizerCode.SemanticStabilizerDistance (sourceValidStabilizer h)
      (binomialTail (r + 1) w) := by sorry
