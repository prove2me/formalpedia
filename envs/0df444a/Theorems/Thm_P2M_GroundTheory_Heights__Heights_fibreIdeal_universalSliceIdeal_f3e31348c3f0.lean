-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreIdeal_universalSliceIdeal_f3e31348c3f0
-- name    : P2M_GroundTheory_Heights__Heights_fibreIdeal_universalSliceIdeal_f3e31348c3f0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:36.847441+00:00
-- url     : https://prove2.me/theorems/4ca10166-da02-428c-bce6-f9c9bfd16bc4
-- title:
--   P2 M Ground Theory Heights  Heights fibre Ideal universal Slice Ideal f3e31348c3f0: P2 M Ground Theory Heights  Heights fibre Ideal universal Slice Ideal f3e31348c3f0
-- statement:
--   The P2 M Ground Theory Heights  Heights fibre Ideal universal Slice Ideal f3e31348c3f0 construction uses the P2 M Ground Theory Heights  Heights fibre Ideal universal Slice Ideal f3e31348c3f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceBundleRadicalAway.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceBundleRadicalAway.lean#L17-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
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
open MvPolynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_fibreIdeal_universalSliceIdeal_f3e31348c3f0 {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (L : Matrix (Fin d) (Fin n) ℂ) :
    fibreIdeal (universalSliceIdeal J d q) (fun ij => L ij.1 ij.2) = sliceIdeal J L q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fibreIdeal_universalSliceIdeal» := P2M_GroundTheory_Heights__Heights_fibreIdeal_universalSliceIdeal_f3e31348c3f0
