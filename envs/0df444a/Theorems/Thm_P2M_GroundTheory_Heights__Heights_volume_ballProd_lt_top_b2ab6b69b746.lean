-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_ballProd_lt_top_b2ab6b69b746
-- name    : P2M_GroundTheory_Heights__Heights_volume_ballProd_lt_top_b2ab6b69b746
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:39.354868+00:00
-- url     : https://prove2.me/theorems/7e5ac44f-84f2-4c13-8d07-6313d1e9a62d
-- title:
--   P2 M Ground Theory Heights  Heights volume ball Prod lt top b2ab6b69b746: P2 M Ground Theory Heights  Heights volume ball Prod lt top b2ab6b69b746
-- statement:
--   The P2 M Ground Theory Heights  Heights volume ball Prod lt top b2ab6b69b746 construction uses the P2 M Ground Theory Heights  Heights volume ball Prod lt top b2ab6b69b746 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean#L79-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
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
open Matrix
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_volume_ballProd_lt_top_b2ab6b69b746 (h : HermNorm n) (k : ℕ) : volume (ballProd h k) < ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«volume_ballProd_lt_top» := P2M_GroundTheory_Heights__Heights_volume_ballProd_lt_top_b2ab6b69b746
