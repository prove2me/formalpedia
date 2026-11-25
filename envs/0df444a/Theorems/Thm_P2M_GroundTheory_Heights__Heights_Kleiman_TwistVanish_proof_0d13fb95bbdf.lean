-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistVanish_proof_0d13fb95bbdf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistVanish_proof_0d13fb95bbdf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:22:32.25352+00:00
-- url     : https://prove2.me/theorems/1aac79a4-177a-502b-9dcd-028f7d4e384c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Vanish proof 0d13fb95bbdf: P2 M Ground Theory Heights  Heights Kleiman Twist Vanish proof 0d13fb95bbdf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Vanish proof 0d13fb95bbdf construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Vanish proof 0d13fb95bbdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistVanish.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistVanish.lean#L14-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistVanish
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
open MvPolynomial
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistVanish_proof_0d13fb95bbdf (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistVanish».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistVanish_proof_0d13fb95bbdf
