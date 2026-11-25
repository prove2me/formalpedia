-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_monotone_56c5f6097949
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_monotone_56c5f6097949
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:45.669905+00:00
-- url     : https://prove2.me/theorems/77fb58e5-5f3c-54ed-834a-ba8376bc0d99
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut monotone 56c5f6097949: P2 M Ground Theory Heights  Heights Slice Cut monotone 56c5f6097949
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut monotone 56c5f6097949 construction uses the P2 M Ground Theory Heights  Heights Slice Cut monotone 56c5f6097949 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceRegMassMono.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceRegMassMono.lean#L14-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegMassMono
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_SliceCut_monotone_56c5f6097949 {n : ℕ} (h : HermNorm n) (x : Fin n → ℂ) : Monotone fun k => sliceCut h k x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«monotone» := P2M_GroundTheory_Heights__Heights_SliceCut_monotone_56c5f6097949
