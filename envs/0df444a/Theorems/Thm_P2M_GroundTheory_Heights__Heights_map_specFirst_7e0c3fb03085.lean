-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_specFirst_7e0c3fb03085
-- name    : P2M_GroundTheory_Heights__Heights_map_specFirst_7e0c3fb03085
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:05:58.236505+00:00
-- url     : https://prove2.me/theorems/7967edac-4296-4425-a248-23d03c361909
-- title:
--   P2 M Ground Theory Heights  Heights map spec First 7e0c3fb03085: P2 M Ground Theory Heights  Heights map spec First 7e0c3fb03085
-- statement:
--   The P2 M Ground Theory Heights  Heights map spec First 7e0c3fb03085 construction uses the P2 M Ground Theory Heights  Heights map spec First 7e0c3fb03085 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecursion.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PRecursion.lean#L14-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecursion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsMultiHomog_specFirst_e9679426b5b5

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

theorem P2M_GroundTheory_Heights__Heights_map_specFirst_7e0c3fb03085 {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {k n : ℕ}
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    MvPolynomial.map φ (specFirst f u) = specFirst (MvPolynomial.map φ f) (fun j => φ (u j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«map_specFirst» := P2M_GroundTheory_Heights__Heights_map_specFirst_7e0c3fb03085
