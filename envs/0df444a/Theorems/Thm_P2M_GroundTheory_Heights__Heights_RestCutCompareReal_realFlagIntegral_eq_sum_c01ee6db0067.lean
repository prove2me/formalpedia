-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_eq_sum_c01ee6db0067
-- name    : P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_eq_sum_c01ee6db0067
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:41.837315+00:00
-- url     : https://prove2.me/theorems/21493dc7-e0d1-5337-8669-360e3322525f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Compare Real real Flag Integral eq sum c01ee6db0067: P2 M Ground Theory Heights  Heights Rest Cut Compare Real real Flag Integral eq sum c01ee6db0067
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Compare Real real Flag Integral eq sum c01ee6db0067 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Compare Real real Flag Integral eq sum c01ee6db0067 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCompareReal.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCompareReal.lean#L22-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCompareReal
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
open GroundTheory.Heights₂.Heights.RestCutCompareReal

theorem P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_eq_sum_c01ee6db0067 (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) :
    realFlagIntegral f N P =
      ∑ α ∈ P.support, realFlagIntegral f N (monomial α (coeff α P)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutCompareReal».«realFlagIntegral_eq_sum» := P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_eq_sum_c01ee6db0067
