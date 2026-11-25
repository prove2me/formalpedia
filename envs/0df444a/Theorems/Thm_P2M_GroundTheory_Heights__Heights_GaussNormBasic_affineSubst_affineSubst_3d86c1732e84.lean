-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_affineSubst_3d86c1732e84
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_affineSubst_3d86c1732e84
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:12.804381+00:00
-- url     : https://prove2.me/theorems/8d3908f9-6438-43e0-a4ba-8f079772cbb8
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic affine Subst affine Subst 3d86c1732e84: P2 M Ground Theory Heights  Heights Gauss Norm Basic affine Subst affine Subst 3d86c1732e84
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic affine Subst affine Subst 3d86c1732e84 construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic affine Subst affine Subst 3d86c1732e84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L99-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L99-L113

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
omit [IsUltrametricDist L]

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_affineSubst_3d86c1732e84 {ι κ μ : Type*} [Fintype κ] [Fintype μ] (B : Matrix ι κ L)
    (a : ι → L) (B' : Matrix κ μ L) (a' : κ → L) (g : MvPolynomial ι L) :
    affineSubst B' a' (affineSubst B a g) = affineSubst (B * B') (B.mulVec a' + a) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«affineSubst_affineSubst» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_affineSubst_3d86c1732e84
