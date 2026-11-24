-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_emb_295f67d8befc
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_emb_295f67d8befc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:02.782952+00:00
-- url     : https://prove2.me/theorems/c2adeb5f-b2a1-4d30-b767-ad69a60dfc64
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale emb 295f67d8befc: P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale emb 295f67d8befc
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale emb 295f67d8befc construction uses the P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale emb 295f67d8befc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L77-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
variable {L : Type} [Field L]
variable {K : Type} [Field K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_emb_295f67d8befc {a : ProjField K i} (ha : a ≠ 0) (x : ProjField K i) :
    scale ha (dualStdModelEmb K i x) = dualStdModelEmb K i x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualModelTranscendence».«scale_emb» := P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_emb_295f67d8befc
