-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_monomial_07607d8d68d0
-- name    : P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_monomial_07607d8d68d0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:49.249215+00:00
-- url     : https://prove2.me/theorems/7b897307-dd92-587c-a66c-1fd6d84868e8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Compare Real real Flag Integral monomial 07607d8d68d0: P2 M Ground Theory Heights  Heights Rest Cut Compare Real real Flag Integral monomial 07607d8d68d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Compare Real real Flag Integral monomial 07607d8d68d0 construction uses the P2 M Ground Theory Heights  Heights Rest Cut Compare Real real Flag Integral monomial 07607d8d68d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCompareReal.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCompareReal.lean#L13-L20

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

theorem P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_monomial_07607d8d68d0 (f N : ℕ) (α : Fin f × Fin N →₀ ℕ) (r : ℝ) :
    realFlagIntegral f N (monomial α r) =
      r * (RestTerms.flagIntegral f N (monomial α (1 : ℚ)) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutCompareReal».«realFlagIntegral_monomial» := P2M_GroundTheory_Heights__Heights_RestCutCompareReal_realFlagIntegral_monomial_07607d8d68d0
