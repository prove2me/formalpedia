-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_pow_le_one_601ccd826390
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_pow_le_one_601ccd826390
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:40.183652+00:00
-- url     : https://prove2.me/theorems/09fe5f6f-e8d2-489d-be8e-0cedde672d74
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm pow le one 601ccd826390: P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm pow le one 601ccd826390
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm pow le one 601ccd826390 construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm pow le one 601ccd826390 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L62-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_pow_le_one_601ccd826390 {ι : Type*} (f : MvPolynomial ι L)
    (h : gaussNormOf (normAbv L) f ≤ 1) (n : ℕ) : gaussNormOf (normAbv L) (f ^ n) ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«gaussNorm_pow_le_one» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_pow_le_one_601ccd826390
