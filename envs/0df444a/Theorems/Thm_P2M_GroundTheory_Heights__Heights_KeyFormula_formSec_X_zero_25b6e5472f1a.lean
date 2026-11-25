-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_formSec_X_zero_25b6e5472f1a
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_formSec_X_zero_25b6e5472f1a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:27:20.180038+00:00
-- url     : https://prove2.me/theorems/19587c2a-f564-475d-9c10-a5b1f09c61fc
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula form Sec X zero 25b6e5472f1a: P2 M Ground Theory Heights  Heights Key Formula form Sec X zero 25b6e5472f1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula form Sec X zero 25b6e5472f1a construction uses the P2 M Ground Theory Heights  Heights Key Formula form Sec X zero 25b6e5472f1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/RigSymFormTauIIsBasisOf.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/RigSymFormTauIIsBasisOf.lean#L25-L28

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

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_formSec_X_zero_25b6e5472f1a :
    rigSymFormTauI.formSec (r := 2) thetaThreeFam (MvPolynomial.X 0) = thetaThreeSec 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«formSec_X_zero» := P2M_GroundTheory_Heights__Heights_KeyFormula_formSec_X_zero_25b6e5472f1a
