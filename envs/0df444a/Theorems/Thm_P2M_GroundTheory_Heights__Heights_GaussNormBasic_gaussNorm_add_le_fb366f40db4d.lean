-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_add_le_fb366f40db4d
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_add_le_fb366f40db4d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:46.010613+00:00
-- url     : https://prove2.me/theorems/e76b956b-6ba5-4075-8e90-fabf52b5002f
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm add le fb366f40db4d: P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm add le fb366f40db4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm add le fb366f40db4d construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm add le fb366f40db4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L21-L27

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

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_add_le_fb366f40db4d {ι : Type*} (g g' : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (g + g') ≤
      max (gaussNormOf (normAbv L) g) (gaussNormOf (normAbv L) g') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«gaussNorm_add_le» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_add_le_fb366f40db4d
