-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplane_proof_3a5c4ef9e989
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplane_proof_3a5c4ef9e989
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:46.680927+00:00
-- url     : https://prove2.me/theorems/fa034508-2dcf-4b67-8aab-2912dbed81ad
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane proof 3a5c4ef9e989: P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane proof 3a5c4ef9e989
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane proof 3a5c4ef9e989 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane proof 3a5c4ef9e989 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L81-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L81-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_proof_063604fa480a

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplane_proof_3a5c4ef9e989 (hA : SnapperQuotAdd.Statement.{u, w, w})
    (hD : SnapperQuotDevissage.Statement.{u, w, w}) (hM : SnapperHyperplaneMid.Statement.{u, w}) :
    SnapperHyperplane.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperHyperplane».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplane_proof_3a5c4ef9e989
