-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FibreSectionsFlat_proof_b7e38112fd9f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FibreSectionsFlat_proof_b7e38112fd9f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:27.78405+00:00
-- url     : https://prove2.me/theorems/d221f3bc-8919-51b9-a1ab-d5e70e4b632f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fibre Sections Flat proof b7e38112fd9f: P2 M Ground Theory Heights  Heights Kleiman Fibre Sections Flat proof b7e38112fd9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fibre Sections Flat proof b7e38112fd9f construction uses the P2 M Ground Theory Heights  Heights Kleiman Fibre Sections Flat proof b7e38112fd9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreSectionsFlat.lean#L43-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreSectionsFlat.lean#L43-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDedekindFibreRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
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
open scoped Pointwise
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FibreSectionsFlat_proof_b7e38112fd9f (hG : GenericRestrLen.Statement.{u, w}) (hK : FibreRestrKer.Statement.{u, w})
    (hT : RestrQuotTorsionFree.Statement.{u, w}) (hR : DedekindFibreRank.Statement.{u, w})
    (hF : FiniteSections.Statement.{u, w}) : FibreSectionsFlat.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FibreSectionsFlat».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_FibreSectionsFlat_proof_b7e38112fd9f
