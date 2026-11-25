-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_mulVec_inv_fcbb3b6fcfcf
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_mulVec_inv_fcbb3b6fcfcf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:28.802641+00:00
-- url     : https://prove2.me/theorems/7f3c25ee-54d7-4b2d-a209-528a909a1879
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut mul Vec inv fcbb3b6fcfcf: P2 M Ground Theory Heights  Heights Slice Cut mul Vec inv fcbb3b6fcfcf
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut mul Vec inv fcbb3b6fcfcf construction uses the P2 M Ground Theory Heights  Heights Slice Cut mul Vec inv fcbb3b6fcfcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L30-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.SliceCut
variable {n : ℕ} (h : HermNorm n)

theorem P2M_GroundTheory_Heights__Heights_SliceCut_mulVec_inv_fcbb3b6fcfcf (x : Fin n → ℂ) : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«mulVec_inv» := P2M_GroundTheory_Heights__Heights_SliceCut_mulVec_inv_fcbb3b6fcfcf
