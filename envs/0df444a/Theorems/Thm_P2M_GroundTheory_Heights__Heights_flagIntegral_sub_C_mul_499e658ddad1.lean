-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_flagIntegral_sub_C_mul_499e658ddad1
-- name    : P2M_GroundTheory_Heights__Heights_flagIntegral_sub_C_mul_499e658ddad1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:18.06632+00:00
-- url     : https://prove2.me/theorems/a985fbda-e698-51c5-a139-24225b356483
-- title:
--   P2 M Ground Theory Heights  Heights flag Integral sub C mul 499e658ddad1: P2 M Ground Theory Heights  Heights flag Integral sub C mul 499e658ddad1
-- statement:
--   The P2 M Ground Theory Heights  Heights flag Integral sub C mul 499e658ddad1 construction uses the P2 M Ground Theory Heights  Heights flag Integral sub C mul 499e658ddad1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutStairNonzero.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutStairNonzero.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutStairNonzero
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

theorem P2M_GroundTheory_Heights__Heights_flagIntegral_sub_C_mul_499e658ddad1 (f N : ℕ) (H S : RestTerms.RootRing f N) (b : ℚ) :
    RestTerms.flagIntegral f N (H - C b * S) =
      RestTerms.flagIntegral f N H - b * RestTerms.flagIntegral f N S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«flagIntegral_sub_C_mul» := P2M_GroundTheory_Heights__Heights_flagIntegral_sub_C_mul_499e658ddad1
