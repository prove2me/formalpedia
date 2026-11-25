-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tanLinPoly_add_3cf296cf920c
-- name    : P2M_GroundTheory_Heights__Heights_tanLinPoly_add_3cf296cf920c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:25.30123+00:00
-- url     : https://prove2.me/theorems/9cef7769-bf0b-4f6e-8ed1-9ab945e80582
-- title:
--   P2 M Ground Theory Heights  Heights tan Lin Poly add 3cf296cf920c: P2 M Ground Theory Heights  Heights tan Lin Poly add 3cf296cf920c
-- statement:
--   The P2 M Ground Theory Heights  Heights tan Lin Poly add 3cf296cf920c construction uses the P2 M Ground Theory Heights  Heights tan Lin Poly add 3cf296cf920c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L52-L53

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

theorem P2M_GroundTheory_Heights__Heights_tanLinPoly_add_3cf296cf920c (p w w' : Fin n → ℂ) : tanLinPoly p (w + w') = tanLinPoly p w + tanLinPoly p w' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tanLinPoly_add» := P2M_GroundTheory_Heights__Heights_tanLinPoly_add_3cf296cf920c
