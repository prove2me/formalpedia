-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_mulVec_injective_e49fb1fd6f50
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_mulVec_injective_e49fb1fd6f50
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:57.78838+00:00
-- url     : https://prove2.me/theorems/1178da11-f6b9-46c8-a21a-f64925600a23
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gram Pos Def mul Vec injective e49fb1fd6f50: P2 M Ground Theory Heights  Heights KLines Gram Pos Def mul Vec injective e49fb1fd6f50
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gram Pos Def mul Vec injective e49fb1fd6f50 construction uses the P2 M Ground Theory Heights  Heights KLines Gram Pos Def mul Vec injective e49fb1fd6f50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGramPosDef.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGramPosDef.lean#L21-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramPosDef
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
open GroundTheory.Heights₂.Heights.KLinesGramPosDef
open Matrix
variable {K : Type*} [Field K] {n : ℕ} {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_mulVec_injective_e49fb1fd6f50 [Fintype ι] (σ : K →+* ℂ) (u : ι → Fin n → K) (hu : LinearIndependent K u) :
    Function.Injective ((Matrix.of fun j a => u a j).map σ).mulVec := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGramPosDef».«mulVec_injective» := P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_mulVec_injective_e49fb1fd6f50
