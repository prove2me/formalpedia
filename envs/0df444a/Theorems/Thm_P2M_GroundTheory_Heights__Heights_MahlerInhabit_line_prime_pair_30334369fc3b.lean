-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_prime_pair_30334369fc3b
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_prime_pair_30334369fc3b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:47:55.862205+00:00
-- url     : https://prove2.me/theorems/ecb8d62a-c50f-5328-b55e-e2feb4d462e9
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit line prime pair 30334369fc3b: P2 M Ground Theory Heights  Heights Mahler Inhabit line prime pair 30334369fc3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit line prime pair 30334369fc3b construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit line prime pair 30334369fc3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L335-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L335-L340

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
open GroundTheory.Heights₂.Heights.MahlerInhabit

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_prime_pair_30334369fc3b :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧ linForm (coord 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (coord 1) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      IsAdmissible (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (coord 0)) (coord 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«line_prime_pair» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_prime_pair_30334369fc3b
