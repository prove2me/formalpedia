-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceRegTailMass_proof_7a1167fe8e03
-- name    : P2M_GroundTheory_Heights__Heights_SliceRegTailMass_proof_7a1167fe8e03
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:19.030805+00:00
-- url     : https://prove2.me/theorems/2be29b6f-237e-431f-b744-eaea4fdc7517
-- title:
--   P2 M Ground Theory Heights  Heights Slice Reg Tail Mass proof 7a1167fe8e03: P2 M Ground Theory Heights  Heights Slice Reg Tail Mass proof 7a1167fe8e03
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Reg Tail Mass proof 7a1167fe8e03 construction uses the P2 M Ground Theory Heights  Heights Slice Reg Tail Mass proof 7a1167fe8e03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceRegTailMass.lean#L15-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceRegTailMass.lean#L15-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegTailMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegMassMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegMassContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegMassLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionTailMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegCutTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutTailMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceRegTailMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceSectionMass_proof_139e377538c6

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

theorem P2M_GroundTheory_Heights__Heights_SliceRegTailMass_proof_7a1167fe8e03 (hMono : SliceRegMassMono.Statement) (hCont : SliceRegMassContinuous.Statement)
    (hLim : SliceRegMassLimit.Statement) (hSec : SliceSectionTailMass.Statement)
    (hReg : SliceRegCutTail.Statement) (hM : SliceCutTailMass.Statement) : SliceRegTailMass.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceRegTailMass».«proof» := P2M_GroundTheory_Heights__Heights_SliceRegTailMass_proof_7a1167fe8e03
