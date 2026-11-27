-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotDevissage_proof_23e5c22c7634
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotDevissage_proof_23e5c22c7634
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:04.143898+00:00
-- url     : https://prove2.me/theorems/6466435a-909d-565d-b04f-26080582a948
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Devissage proof 23e5c22c7634: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Devissage proof 23e5c22c7634
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Devissage proof 23e5c22c7634 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Devissage proof 23e5c22c7634 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotDevissage.lean#L50-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotDevissage.lean#L50-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotDevissage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Snapper_proof_919ee0f6bfe6

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotDevissage_proof_23e5c22c7634 (hF : SnapperQuotFilt.Statement.{u, v, w})
    (hI : SnapperQuotIso.Statement.{u, v, w, w}) (hA : SnapperQuotAdd.Statement.{u, v, w})
    (hB : SubFamilyTwist.Statement.{u, v, w}) : SnapperQuotDevissage.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotDevissage».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotDevissage_proof_23e5c22c7634
