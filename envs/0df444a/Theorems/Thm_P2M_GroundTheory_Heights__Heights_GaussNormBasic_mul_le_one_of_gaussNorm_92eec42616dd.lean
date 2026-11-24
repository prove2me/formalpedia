-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_mul_le_one_of_gaussNorm_92eec42616dd
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_mul_le_one_of_gaussNorm_92eec42616dd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:02.10633+00:00
-- url     : https://prove2.me/theorems/2d784d4d-b5ca-4c6e-ae90-8b517e4d7198
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic mul le one of gauss Norm 92eec42616dd: P2 M Ground Theory Heights  Heights Gauss Norm Basic mul le one of gauss Norm 92eec42616dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic mul le one of gauss Norm 92eec42616dd construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic mul le one of gauss Norm 92eec42616dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L50-L54

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

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_mul_le_one_of_gaussNorm_92eec42616dd {ι : Type*} {a b : MvPolynomial ι L}
    (ha : gaussNormOf (normAbv L) a ≤ 1) (hb : gaussNormOf (normAbv L) b ≤ 1) :
    gaussNormOf (normAbv L) (a * b) ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«mul_le_one_of_gaussNorm» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_mul_le_one_of_gaussNorm_92eec42616dd
