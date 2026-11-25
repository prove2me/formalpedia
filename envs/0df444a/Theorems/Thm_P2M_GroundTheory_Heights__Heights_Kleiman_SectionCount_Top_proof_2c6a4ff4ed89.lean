-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Top_proof_2c6a4ff4ed89
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Top_proof_2c6a4ff4ed89
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:50.266856+00:00
-- url     : https://prove2.me/theorems/639a1daa-ba8b-4688-93e4-074d834d08f3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Top proof 2c6a4ff4ed89: P2 M Ground Theory Heights  Heights Kleiman Section Count Top proof 2c6a4ff4ed89
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Top proof 2c6a4ff4ed89 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Top proof 2c6a4ff4ed89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L95-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L95-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Top_proof_2c6a4ff4ed89 (hHP : HilbertPositive.Statement.{u, w})
    (hTie : InterNumTie.Statement.{u, w}) (hTF : TwistFinite.Statement.{u, w})
    (hDim : VeryAmpleDim.Statement.{u, w}) (hDeg : VeryAmpleDegree.Statement.{u, w}) :
    SectionCount.Top.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Top».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Top_proof_2c6a4ff4ed89
