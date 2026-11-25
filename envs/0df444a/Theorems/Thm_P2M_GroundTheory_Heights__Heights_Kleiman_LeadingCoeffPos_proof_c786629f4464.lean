-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LeadingCoeffPos_proof_c786629f4464
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LeadingCoeffPos_proof_c786629f4464
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:51.845884+00:00
-- url     : https://prove2.me/theorems/f97fc4f5-865d-5255-81a6-1c0680975f8a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Leading Coeff Pos proof c786629f4464: P2 M Ground Theory Heights  Heights Kleiman Leading Coeff Pos proof c786629f4464
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Leading Coeff Pos proof c786629f4464 construction uses the P2 M Ground Theory Heights  Heights Kleiman Leading Coeff Pos proof c786629f4464 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLeadingCoeffPos.lean#L23-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLeadingCoeffPos.lean#L23-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleProductPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLeadingCoeffPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_NefProductNonneg_proof_7c92517c4d22

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
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LeadingCoeffPos_proof_c786629f4464 (hR : GenericPointSectionInput.Statement.{u, w})
    (hNef : NefProductNonneg.Statement.{u, w}) (hPos : VeryAmpleProductPos.Statement.{u, w}) :
    LeadingCoeffPos.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LeadingCoeffPos».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_LeadingCoeffPos_proof_c786629f4464
