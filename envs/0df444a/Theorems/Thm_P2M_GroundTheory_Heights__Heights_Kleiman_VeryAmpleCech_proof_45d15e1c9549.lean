-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleCech_proof_45d15e1c9549
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleCech_proof_45d15e1c9549
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:30:15.805688+00:00
-- url     : https://prove2.me/theorems/a7ad83c7-ec4e-567b-a3e3-b231413324ac
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Cech proof 45d15e1c9549: P2 M Ground Theory Heights  Heights Kleiman Very Ample Cech proof 45d15e1c9549
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Cech proof 45d15e1c9549 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Cech proof 45d15e1c9549 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleCech.lean#L18-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleCech.lean#L18-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistPowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechHdegOfSubSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZRowsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleCech
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleCech_proof_45d15e1c9549 (hFam : VeryAmpleZFamily.Statement.{u, v, w})
    (hFin : VeryAmpleZFinite.Statement.{u, v, w}) (hTw : VeryAmpleZTwist.Statement.{u, v, w})
    (hPow : SubFamilyTwistPow.Statement.{u, v, w}) (hSub : CechHdegOfSub.Statement.{u, v, w})
    (hDbl : CechDouble.Statement.{u, v, w}) (hCol : VeryAmpleZColumns.Statement.{u, v, w})
    (hRow : VeryAmpleZRows.Statement.{u, v, w}) : VeryAmpleCech.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleCech».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleCech_proof_45d15e1c9549
