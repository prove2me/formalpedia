-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_vertTerm_nonneg_4d532362fa73
-- name    : P2M_GroundTheory_Heights__Heights_vertTerm_nonneg_4d532362fa73
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:26.752056+00:00
-- url     : https://prove2.me/theorems/ddd3c26a-3bb4-54be-bc1a-491a06b8dbaa
-- title:
--   P2 M Ground Theory Heights  Heights vert Term nonneg 4d532362fa73: P2 M Ground Theory Heights  Heights vert Term nonneg 4d532362fa73
-- statement:
--   The P2 M Ground Theory Heights  Heights vert Term nonneg 4d532362fa73 construction uses the P2 M Ground Theory Heights  Heights vert Term nonneg 4d532362fa73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L202-L206

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_vertTerm_nonneg_4d532362fa73 (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) (u : Fin n → 𝓞 K) :
    0 ≤ vertTerm I k u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«vertTerm_nonneg» := P2M_GroundTheory_Heights__Heights_vertTerm_nonneg_4d532362fa73
