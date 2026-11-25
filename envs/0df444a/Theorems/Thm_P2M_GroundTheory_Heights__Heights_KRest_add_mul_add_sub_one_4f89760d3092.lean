-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_add_mul_add_sub_one_4f89760d3092
-- name    : P2M_GroundTheory_Heights__Heights_KRest_add_mul_add_sub_one_4f89760d3092
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:57.502176+00:00
-- url     : https://prove2.me/theorems/387bed69-1fc8-46c9-9883-c360e573b50d
-- title:
--   P2 M Ground Theory Heights  Heights KRest add mul add sub one 4f89760d3092: P2 M Ground Theory Heights  Heights KRest add mul add sub one 4f89760d3092
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest add mul add sub one 4f89760d3092 construction uses the P2 M Ground Theory Heights  Heights KRest add mul add sub one 4f89760d3092 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutRestHom.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutRestHom.lean#L20-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutRestHom
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
open GroundTheory.Heights₂.Heights.KRest

theorem P2M_GroundTheory_Heights__Heights_KRest_add_mul_add_sub_one_4f89760d3092 (r a : ℕ) :
    (r + a) * (r + a - 1) = r * (r - 1) + a * (a - 1) + 2 * (r * a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«add_mul_add_sub_one» := P2M_GroundTheory_Heights__Heights_KRest_add_mul_add_sub_one_4f89760d3092
