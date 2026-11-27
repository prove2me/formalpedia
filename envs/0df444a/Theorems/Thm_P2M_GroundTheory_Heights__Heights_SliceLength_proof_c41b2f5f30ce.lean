-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLength_proof_c41b2f5f30ce
-- name    : P2M_GroundTheory_Heights__Heights_SliceLength_proof_c41b2f5f30ce
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:38:02.37024+00:00
-- url     : https://prove2.me/theorems/8cfc87b2-7118-4b9b-a6f8-f9ae80a03740
-- title:
--   P2 M Ground Theory Heights  Heights Slice Length proof c41b2f5f30ce: P2 M Ground Theory Heights  Heights Slice Length proof c41b2f5f30ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Length proof c41b2f5f30ce construction uses the P2 M Ground Theory Heights  Heights Slice Length proof c41b2f5f30ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLength.lean#L12-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLength.lean#L12-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets

theorem P2M_GroundTheory_Heights__Heights_SliceLength_proof_c41b2f5f30ce (hV : IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement)
    (hR : SliceReducedGeneral.Statement) (hM : SliceMultGeneral.Statement) :
    SliceLength.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceLength».«proof» := P2M_GroundTheory_Heights__Heights_SliceLength_proof_c41b2f5f30ce
