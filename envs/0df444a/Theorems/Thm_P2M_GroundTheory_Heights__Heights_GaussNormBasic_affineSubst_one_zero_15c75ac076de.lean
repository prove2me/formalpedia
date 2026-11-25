-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_one_zero_15c75ac076de
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_one_zero_15c75ac076de
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:51.3708+00:00
-- url     : https://prove2.me/theorems/37dc919b-9606-45bb-99cf-5b45ddaa77aa
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic affine Subst one zero 15c75ac076de: P2 M Ground Theory Heights  Heights Gauss Norm Basic affine Subst one zero 15c75ac076de
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic affine Subst one zero 15c75ac076de construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic affine Subst one zero 15c75ac076de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L117-L125

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

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_one_zero_15c75ac076de {ι : Type*} [Fintype ι] [DecidableEq ι] (g : MvPolynomial ι L) :
    affineSubst (1 : Matrix ι ι L) 0 g = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«affineSubst_one_zero» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_affineSubst_one_zero_15c75ac076de
