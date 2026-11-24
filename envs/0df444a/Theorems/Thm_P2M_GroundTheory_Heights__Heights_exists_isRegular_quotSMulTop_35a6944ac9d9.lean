-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_isRegular_quotSMulTop_35a6944ac9d9
-- name    : P2M_GroundTheory_Heights__Heights_exists_isRegular_quotSMulTop_35a6944ac9d9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:01.321838+00:00
-- url     : https://prove2.me/theorems/0262cab2-5d9b-4550-98de-cff36a4dc71d
-- title:
--   P2 M Ground Theory Heights  Heights exists is Regular quot SMul Top 35a6944ac9d9: P2 M Ground Theory Heights  Heights exists is Regular quot SMul Top 35a6944ac9d9
-- statement:
--   The P2 M Ground Theory Heights  Heights exists is Regular quot SMul Top 35a6944ac9d9 construction uses the P2 M Ground Theory Heights  Heights exists is Regular quot SMul Top 35a6944ac9d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMRegularElement.lean#L61-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMRegularElement.lean#L61-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
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
open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise
universe u

theorem P2M_GroundTheory_Heights__Heights_exists_isRegular_quotSMulTop_35a6944ac9d9 {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {rs : List B} (hm : ∀ r ∈ rs, r ∈ maximalIdeal B) (hreg : IsWeaklyRegular B rs)
    {y : B} (hy : IsSMulRegular B y) (hym : y ∈ maximalIdeal B) :
    ∃ rs' : List B, rs'.length = rs.length - 1 ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧
      IsRegular (QuotSMulTop y B) rs' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_isRegular_quotSMulTop» := P2M_GroundTheory_Heights__Heights_exists_isRegular_quotSMulTop_35a6944ac9d9
