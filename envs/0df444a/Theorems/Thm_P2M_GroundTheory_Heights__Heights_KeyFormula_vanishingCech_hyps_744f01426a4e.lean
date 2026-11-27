-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_vanishingCech_hyps_744f01426a4e
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_vanishingCech_hyps_744f01426a4e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:26:18.070651+00:00
-- url     : https://prove2.me/theorems/65b62db8-7074-46cf-8977-a865445de17a
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula vanishing Cech hyps 744f01426a4e: P2 M Ground Theory Heights  Heights Key Formula vanishing Cech hyps 744f01426a4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula vanishing Cech hyps 744f01426a4e construction uses the P2 M Ground Theory Heights  Heights Key Formula vanishing Cech hyps 744f01426a4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/RigSymFormTauIIsBasisOf.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/RigSymFormTauIIsBasisOf.lean#L16-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauIIsBasisOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_vanishingCech_hyps_744f01426a4e :
    rigSymFormTauI.g = 1 ∧ 3 ≤ 3 ∧ rigSymFormTauI.IsBasisOf 3 (r := 2) thetaThreeFam ∧ 1 ≤ 1 ∧
      rigSymFormTauI.IsCocycle 3 1 (0 + 1) thetaThreeFam (fun _ _ => 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«vanishingCech_hyps» := P2M_GroundTheory_Heights__Heights_KeyFormula_vanishingCech_hyps_744f01426a4e
