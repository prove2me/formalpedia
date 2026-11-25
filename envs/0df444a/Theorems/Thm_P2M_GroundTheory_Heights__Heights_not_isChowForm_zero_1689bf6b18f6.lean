-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_isChowForm_zero_1689bf6b18f6
-- name    : P2M_GroundTheory_Heights__Heights_not_isChowForm_zero_1689bf6b18f6
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:50.135969+00:00
-- url     : https://prove2.me/theorems/1111b27a-db95-5a85-b10c-c02a01af40b4
-- title:
--   P2 M Ground Theory Heights  Heights not is Chow Form zero 1689bf6b18f6: P2 M Ground Theory Heights  Heights not is Chow Form zero 1689bf6b18f6
-- statement:
--   The P2 M Ground Theory Heights  Heights not is Chow Form zero 1689bf6b18f6 construction uses the P2 M Ground Theory Heights  Heights not is Chow Form zero 1689bf6b18f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PCharacterised.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PCharacterised.lean#L13-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCharacterised
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

theorem P2M_GroundTheory_Heights__Heights_not_isChowForm_zero_1689bf6b18f6 (hPt : ProjPrimeHasPoint.Statement) {F : Type} [Field F] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) F)} (hW : IsProjPrime W) (g : MvPolynomial (Fin 0 × Fin n) F) :
    ¬ IsChowForm W 0 g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«not_isChowForm_zero» := P2M_GroundTheory_Heights__Heights_not_isChowForm_zero_1689bf6b18f6
