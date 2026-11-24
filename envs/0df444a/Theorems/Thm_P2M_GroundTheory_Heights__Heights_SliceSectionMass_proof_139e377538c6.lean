-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceSectionMass_proof_139e377538c6
-- name    : P2M_GroundTheory_Heights__Heights_SliceSectionMass_proof_139e377538c6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:01.331793+00:00
-- url     : https://prove2.me/theorems/b61aa446-001f-41fa-9908-ad6caa5d9ed4
-- title:
--   P2 M Ground Theory Heights  Heights Slice Section Mass proof 139e377538c6: P2 M Ground Theory Heights  Heights Slice Section Mass proof 139e377538c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Section Mass proof 139e377538c6 construction uses the P2 M Ground Theory Heights  Heights Slice Section Mass proof 139e377538c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceSectionMass.lean#L40-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceSectionMass.lean#L40-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceExhaustion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
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
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_SliceSectionMass_proof_139e377538c6 (hSt : StokesOnVariety.Statement) (hPL : PoincareLelong.Statement)
    (hI : SliceIdeal.Statement) (hC : SliceComponents.Statement) (hE : SliceExhaustion.Statement) :
    SliceSectionMass.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceSectionMass».«proof» := P2M_GroundTheory_Heights__Heights_SliceSectionMass_proof_139e377538c6
