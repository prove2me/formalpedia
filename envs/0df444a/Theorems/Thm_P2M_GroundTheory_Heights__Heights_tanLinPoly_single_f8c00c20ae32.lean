-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tanLinPoly_single_f8c00c20ae32
-- name    : P2M_GroundTheory_Heights__Heights_tanLinPoly_single_f8c00c20ae32
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:29.369638+00:00
-- url     : https://prove2.me/theorems/f7af246f-ee70-4b06-a5dc-26a2a81babb3
-- title:
--   P2 M Ground Theory Heights  Heights tan Lin Poly single f8c00c20ae32: P2 M Ground Theory Heights  Heights tan Lin Poly single f8c00c20ae32
-- statement:
--   The P2 M Ground Theory Heights  Heights tan Lin Poly single f8c00c20ae32 construction uses the P2 M Ground Theory Heights  Heights tan Lin Poly single f8c00c20ae32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L61-L65

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

theorem P2M_GroundTheory_Heights__Heights_tanLinPoly_single_f8c00c20ae32 (p : Fin n → ℂ) (i : Fin n) :
    tanLinPoly p (Pi.single i 1) = X i - C (p i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tanLinPoly_single» := P2M_GroundTheory_Heights__Heights_tanLinPoly_single_f8c00c20ae32
