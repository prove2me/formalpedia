-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Snapper_proof_919ee0f6bfe6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Snapper_proof_919ee0f6bfe6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:49.988946+00:00
-- url     : https://prove2.me/theorems/e2115257-7b49-4d5f-b702-662f23bcb40a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper proof 919ee0f6bfe6: P2 M Ground Theory Heights  Heights Kleiman Snapper proof 919ee0f6bfe6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper proof 919ee0f6bfe6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper proof 919ee0f6bfe6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L185-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L185-L199

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
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
universe u v w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Snapper_proof_919ee0f6bfe6 (hD : SnapperDevissage.Statement.{u, v, w}) (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) (hP : SnapperDiffPoly.Statement) : Snapper.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Snapper».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_Snapper_proof_919ee0f6bfe6
