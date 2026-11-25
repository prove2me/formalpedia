-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDegree_proof_8023612bf403
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDegree_proof_8023612bf403
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:07:51.928412+00:00
-- url     : https://prove2.me/theorems/72a33021-2b4c-5e3f-8838-fe9113924a3d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Degree proof 8023612bf403: P2 M Ground Theory Heights  Heights Kleiman Very Ample Degree proof 8023612bf403
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Degree proof 8023612bf403 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Degree proof 8023612bf403 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDegree.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDegree.lean#L16-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleHilbertSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDegree_proof_8023612bf403 (hDim : VeryAmpleDim.Statement.{u, w})
    (hSecs : VeryAmpleSecs.Statement.{u, w}) (hHilb : VeryAmpleHilbert.Statement.{u, w}) :
    VeryAmpleDegree.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleDegree».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDegree_proof_8023612bf403
