-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyConjugationInvariant_fsMetric_conj_c938287a366d
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyConjugationInvariant_fsMetric_conj_c938287a366d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:19.814869+00:00
-- url     : https://prove2.me/theorems/1f58ebff-0fd9-58ae-87a3-23c0b5fdce1e
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Conjugation Invariant fs Metric conj c938287a366d: P2 M Ground Theory Heights  Heights Fubini Study Conjugation Invariant fs Metric conj c938287a366d
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Conjugation Invariant fs Metric conj c938287a366d construction uses the P2 M Ground Theory Heights  Heights Fubini Study Conjugation Invariant fs Metric conj c938287a366d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PFsConjInvariant.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PFsConjInvariant.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PFsConjInvariant
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
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.FubiniStudyConjugationInvariant

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyConjugationInvariant_fsMetric_conj_c938287a366d {n : Type*} [Fintype n] (w : n → ℂ) :
    (fsMetric n).ρ (fun i => (starRingEnd ℂ) (w i)) = (fsMetric n).ρ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyConjugationInvariant».«fsMetric_conj» := P2M_GroundTheory_Heights__Heights_FubiniStudyConjugationInvariant_fsMetric_conj_c938287a366d
