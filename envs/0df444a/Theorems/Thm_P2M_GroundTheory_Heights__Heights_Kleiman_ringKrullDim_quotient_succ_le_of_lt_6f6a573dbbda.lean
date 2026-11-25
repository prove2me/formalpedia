-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quotient_succ_le_of_lt_6f6a573dbbda
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quotient_succ_le_of_lt_6f6a573dbbda
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:11:09.295604+00:00
-- url     : https://prove2.me/theorems/a64a7376-0031-5661-8556-46900261d602
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ring Krull Dim quotient succ le of lt 6f6a573dbbda: P2 M Ground Theory Heights  Heights Kleiman ring Krull Dim quotient succ le of lt 6f6a573dbbda
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ring Krull Dim quotient succ le of lt 6f6a573dbbda construction uses the P2 M Ground Theory Heights  Heights Kleiman ring Krull Dim quotient succ le of lt 6f6a573dbbda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L73-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L73-L85

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
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quotient_succ_le_of_lt_6f6a573dbbda {pp qq : Ideal R} [pp.IsPrime] (h : pp < qq) :
    ringKrullDim (R ⧸ qq) + 1 ≤ ringKrullDim (R ⧸ pp) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ringKrullDim_quotient_succ_le_of_lt» := P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quotient_succ_le_of_lt_6f6a573dbbda
