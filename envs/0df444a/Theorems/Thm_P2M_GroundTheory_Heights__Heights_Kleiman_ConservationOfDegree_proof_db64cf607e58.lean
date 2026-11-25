-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ConservationOfDegree_proof_db64cf607e58
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ConservationOfDegree_proof_db64cf607e58
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:35.404267+00:00
-- url     : https://prove2.me/theorems/2a26c494-32f2-507a-9993-95cd94ecef13
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Conservation Of Degree proof db64cf607e58: P2 M Ground Theory Heights  Heights Kleiman Conservation Of Degree proof db64cf607e58
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Conservation Of Degree proof db64cf607e58 construction uses the P2 M Ground Theory Heights  Heights Kleiman Conservation Of Degree proof db64cf607e58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PConservationOfDegree.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PConservationOfDegree.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsNefGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreHilbertFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreCycleDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PConservationOfDegree
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ConservationOfDegree_proof_db64cf607e58 (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : ConservationOfDegree.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ConservationOfDegree».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_ConservationOfDegree_proof_db64cf607e58
