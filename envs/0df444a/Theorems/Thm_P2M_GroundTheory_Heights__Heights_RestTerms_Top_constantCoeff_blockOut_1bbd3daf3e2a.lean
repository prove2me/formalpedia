-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_blockOut_1bbd3daf3e2a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_blockOut_1bbd3daf3e2a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:57.573008+00:00
-- url     : https://prove2.me/theorems/2665ead4-de54-427a-94a4-c7b6ba92c118
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff block Out 1bbd3daf3e2a: P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff block Out 1bbd3daf3e2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff block Out 1bbd3daf3e2a construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff block Out 1bbd3daf3e2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L371-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L371-L377

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_blockOut_1bbd3daf3e2a (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) :
    constantCoeff (blockOut r a c κ q m) =
      if q + m = r * a then blockCoeff q m (rectangle r a) * κ else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«constantCoeff_blockOut» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_blockOut_1bbd3daf3e2a
