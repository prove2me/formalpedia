-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_affineSubst_le_685f1ed1ce28
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_affineSubst_le_685f1ed1ce28
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:34.557731+00:00
-- url     : https://prove2.me/theorems/3a13da0d-d440-4361-9bec-458d926c1886
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm affine Subst le 685f1ed1ce28: P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm affine Subst le 685f1ed1ce28
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm affine Subst le 685f1ed1ce28 construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm affine Subst le 685f1ed1ce28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L92-L95

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

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_affineSubst_le_685f1ed1ce28 {ι κ : Type*} [Fintype κ] (B : Matrix ι κ L) (a : ι → L)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (ha : ∀ i, ‖a i‖ ≤ 1) (g : MvPolynomial ι L) :
    gaussNormOf (normAbv L) (affineSubst B a g) ≤ gaussNormOf (normAbv L) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«gaussNorm_affineSubst_le» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_affineSubst_le_685f1ed1ce28
