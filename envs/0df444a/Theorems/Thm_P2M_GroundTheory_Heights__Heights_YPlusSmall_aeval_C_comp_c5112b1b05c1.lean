-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_C_comp_c5112b1b05c1
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_C_comp_c5112b1b05c1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:49.108066+00:00
-- url     : https://prove2.me/theorems/f0b72efa-6fe9-424c-bed0-3c5868b5ea48
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Small aeval C comp c5112b1b05c1: P2 M Ground Theory Heights  Heights YPlus Small aeval C comp c5112b1b05c1
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Small aeval C comp c5112b1b05c1 construction uses the P2 M Ground Theory Heights  Heights YPlus Small aeval C comp c5112b1b05c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L30-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall

theorem P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_C_comp_c5112b1b05c1 {σ : Type*} {Ω : Type*} [Field Ω] {ι : Type*} (v : σ → Ω) (F : MvPolynomial σ ℤ) :
    aeval (fun p ↦ (C (v p) : MvPolynomial ι Ω)) F = C (aeval v F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSmall».«aeval_C_comp» := P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_C_comp_c5112b1b05c1
