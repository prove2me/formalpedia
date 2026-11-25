-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_proof_570df861e8c8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_proof_570df861e8c8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:46.454718+00:00
-- url     : https://prove2.me/theorems/bbb94a6f-ef58-554f-be52-8a2ac4bd0553
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ZChart Local proof 570df861e8c8: P2 M Ground Theory Heights  Heights Kleiman ZChart Local proof 570df861e8c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ZChart Local proof 570df861e8c8 construction uses the P2 M Ground Theory Heights  Heights Kleiman ZChart Local proof 570df861e8c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L110-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L110-L163

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZChartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_proof_1c887bca4a14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e

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
noncomputable section
universe u v w
open AmpleAffineGen AmpleTwistLocal ZChartLocal

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_proof_570df861e8c8 (hSmul : ZChartSmul.Statement.{u, v, w}) : ZChartLocal.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ZChartLocal».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_proof_570df861e8c8
