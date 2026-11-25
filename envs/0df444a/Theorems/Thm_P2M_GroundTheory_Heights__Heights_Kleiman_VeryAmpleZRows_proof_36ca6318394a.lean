-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_proof_36ca6318394a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_proof_36ca6318394a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:00:04.001717+00:00
-- url     : https://prove2.me/theorems/5935babe-11af-458f-84e7-1d3b346b560c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows proof 36ca6318394a: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows proof 36ca6318394a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows proof 36ca6318394a construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows proof 36ca6318394a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L67-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L67-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZRowsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZRows
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
open VeryAmpleZRows

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_proof_36ca6318394a (hPart : CechPartition.Statement.{u, v, w}) (hSmul : ZChartSmul.Statement.{u, v, w})
    (hLoc : ZChartLocal.Statement.{u, v, w}) : VeryAmpleZRows.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZRows».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_proof_36ca6318394a
