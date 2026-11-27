-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSnapper_proof_c990f3b5fcc4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSnapper_proof_c990f3b5fcc4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:30:53.90375+00:00
-- url     : https://prove2.me/theorems/95dcecb6-2ef9-58a1-b4a8-4852b7f4f199
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Snapper proof c990f3b5fcc4: P2 M Ground Theory Heights  Heights Kleiman Very Ample Snapper proof c990f3b5fcc4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Snapper proof c990f3b5fcc4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Snapper proof c990f3b5fcc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSnapper.lean#L25-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleSnapper.lean#L25-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSnapperSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSnapper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_proof_666dbd5f83b0

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
open MvPolynomial Filter
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSnapper_proof_c990f3b5fcc4 (hF : SnapperFinite.Statement.{u, w, w}) (hS : Snapper.Statement.{u, w, w})
    (hV : TwistVanishAll.Statement.{u, w}) (hA : AmpleVanish.Statement.{u, w, w}) :
    VeryAmpleSnapper.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleSnapper».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSnapper_proof_c990f3b5fcc4
