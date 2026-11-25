-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_pointIdeal_blockIncl_bac95bce694c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_pointIdeal_blockIncl_bac95bce694c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:34:02.936956+00:00
-- url     : https://prove2.me/theorems/fa1816ab-ea02-48bb-a43a-4b3581f2fee1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR comap point Ideal block Incl bac95bce694c: P2 M Ground Theory Heights  Heights Numbers DVR comap point Ideal block Incl bac95bce694c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR comap point Ideal block Incl bac95bce694c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR comap point Ideal block Incl bac95bce694c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSegreFlagCutLiesOver.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSegreFlagCutLiesOver.lean#L23-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagCutProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagCutLiesOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_pointIdeal_blockIncl_bac95bce694c {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K K' : Type*}
    (j : K ↪ K') {ι' : K' → Type*} (pt : (Σ k', ι' k') → Φ) :
    (pointIdeal R pt).comap (rename (FieldNumbers.blockIncl j ι')) =
      pointIdeal R (fun p => pt (FieldNumbers.blockIncl j ι' p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«comap_pointIdeal_blockIncl» := P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_pointIdeal_blockIncl_bac95bce694c
