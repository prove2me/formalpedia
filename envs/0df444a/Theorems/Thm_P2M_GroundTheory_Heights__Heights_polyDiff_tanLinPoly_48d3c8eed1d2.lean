-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_polyDiff_tanLinPoly_48d3c8eed1d2
-- name    : P2M_GroundTheory_Heights__Heights_polyDiff_tanLinPoly_48d3c8eed1d2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:15.331097+00:00
-- url     : https://prove2.me/theorems/2fb572ae-43d7-5c4e-94db-0a2b0987a666
-- title:
--   P2 M Ground Theory Heights  Heights poly Diff tan Lin Poly 48d3c8eed1d2: P2 M Ground Theory Heights  Heights poly Diff tan Lin Poly 48d3c8eed1d2
-- statement:
--   The P2 M Ground Theory Heights  Heights poly Diff tan Lin Poly 48d3c8eed1d2 construction uses the P2 M Ground Theory Heights  Heights poly Diff tan Lin Poly 48d3c8eed1d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L67-L70

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

theorem P2M_GroundTheory_Heights__Heights_polyDiff_tanLinPoly_48d3c8eed1d2 (p w : Fin n → ℂ) : polyDiff p (tanLinPoly p w) = w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«polyDiff_tanLinPoly» := P2M_GroundTheory_Heights__Heights_polyDiff_tanLinPoly_48d3c8eed1d2
