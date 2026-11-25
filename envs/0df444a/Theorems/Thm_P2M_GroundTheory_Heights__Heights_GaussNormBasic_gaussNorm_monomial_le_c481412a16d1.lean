-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_monomial_le_c481412a16d1
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_monomial_le_c481412a16d1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:48.736259+00:00
-- url     : https://prove2.me/theorems/9610579f-87ae-44b8-a31a-8cabb65912ee
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm monomial le c481412a16d1: P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm monomial le c481412a16d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm monomial le c481412a16d1 construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm monomial le c481412a16d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L38-L43

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

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_monomial_le_c481412a16d1 {ι : Type*} (d : ι →₀ ℕ) (b : L) :
    gaussNormOf (normAbv L) (monomial d b) ≤ ‖b‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«gaussNorm_monomial_le» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_monomial_le_c481412a16d1
