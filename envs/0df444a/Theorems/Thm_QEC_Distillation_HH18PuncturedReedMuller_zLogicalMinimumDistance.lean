-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_zLogicalMinimumDistance
-- name    : QEC.Distillation.HH18PuncturedReedMuller.zLogicalMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:51:21.230296+00:00
-- url     : https://prove2.me/theorems/7b4c0c47-fc59-4d83-9bc4-490bfde629ba
-- title:
--   HH18 Punctured Reed Muller: z Logical Minimum Distance
-- statement:
--   The attained Z-logical distance is the complementary punctured
--   Reed--Muller coset distance for the actual HH18 parity-check presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L274-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L274-L303

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

theorem QEC.Distillation.HH18PuncturedReedMuller.zLogicalMinimumDistance {w r m : Nat} (h : Admissible w r m) :
    CSSZLogicalMinimumDistance (zParityCheck w r m) (xParityCheck w r m)
      (binomialTail (r + 1) w) := by sorry
