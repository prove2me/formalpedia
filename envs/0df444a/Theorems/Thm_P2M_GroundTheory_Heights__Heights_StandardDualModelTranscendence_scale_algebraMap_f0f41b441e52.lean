-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_algebraMap_f0f41b441e52
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_algebraMap_f0f41b441e52
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:54.885843+00:00
-- url     : https://prove2.me/theorems/6693db50-3dda-4fec-b3b1-db6966779399
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale algebra Map f0f41b441e52: P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale algebra Map f0f41b441e
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale algebra Map f0f41b441e52 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale algebra Map f0f41b441e52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L51-L53

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_algebraMap_f0f41b441e52 {a : L} (ha : a ≠ 0) (p : MvPolynomial Unit (MvPolynomial Unit L)) :
    scale ha (algebraMap _ _ p) = algebraMap _ _ (scaleHom a p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualModelTranscendence».«scale_algebraMap» := P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_algebraMap_f0f41b441e52
