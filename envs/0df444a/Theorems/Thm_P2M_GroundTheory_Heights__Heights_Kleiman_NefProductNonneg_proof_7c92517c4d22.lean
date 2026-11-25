-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_NefProductNonneg_proof_7c92517c4d22
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_NefProductNonneg_proof_7c92517c4d22
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:35:56.695055+00:00
-- url     : https://prove2.me/theorems/99c8c2d7-1830-4d23-bebf-dbe8c1811680
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Nef Product Nonneg proof 7c92517c4d22: P2 M Ground Theory Heights  Heights Kleiman Nef Product Nonneg proof 7c92517c4d22
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Nef Product Nonneg proof 7c92517c4d22 construction uses the P2 M Ground Theory Heights  Heights Kleiman Nef Product Nonneg proof 7c92517c4d22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L213-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L213-L265

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_NefProductNonneg_proof_7c92517c4d22 (hK : VeryAmpleNefPlusAmple.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : NefProductNonneg.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«NefProductNonneg».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_NefProductNonneg_proof_7c92517c4d22
