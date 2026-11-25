-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_tanLinPoly_ed1f22825e97
-- name    : P2M_GroundTheory_Heights__Heights_eval_tanLinPoly_ed1f22825e97
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:38.765622+00:00
-- url     : https://prove2.me/theorems/aef2dbb7-92f4-5645-9cbf-b34ec9a790c0
-- title:
--   P2 M Ground Theory Heights  Heights eval tan Lin Poly ed1f22825e97: P2 M Ground Theory Heights  Heights eval tan Lin Poly ed1f22825e97
-- statement:
--   The P2 M Ground Theory Heights  Heights eval tan Lin Poly ed1f22825e97 construction uses the P2 M Ground Theory Heights  Heights eval tan Lin Poly ed1f22825e97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L49-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_eval_tanLinPoly_ed1f22825e97 (p w : Fin n → ℂ) : eval p (tanLinPoly p w) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_tanLinPoly» := P2M_GroundTheory_Heights__Heights_eval_tanLinPoly_ed1f22825e97
