-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_X_dvd_of_substZeroZeroZero_eq_zero_e00626ca4948
-- name    : P2M_GroundTheory_Heights__Heights_LineChowForm_X_dvd_of_substZeroZeroZero_eq_zero_e00626ca4948
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:27.529818+00:00
-- url     : https://prove2.me/theorems/8d90f45d-16ac-5407-ad4a-92f5b727788c
-- title:
--   P2 M Ground Theory Heights  Heights Line Chow Form X dvd of subst Zero Zero Zero eq zero e00626ca4948: P2 M Ground Theory Heights  Heights Line Chow Form X dvd of subst Zero Zero Zero eq zero e00626ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Chow Form X dvd of subst Zero Zero Zero eq zero e00626ca4948 construction uses the P2 M Ground Theory Heights  Heights Line Chow Form X dvd of subst Zero Zero Zero eq zero e00626ca4948 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L25-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LineInhabitant.lean#L25-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_LineChowForm_X_dvd_of_substZeroZeroZero_eq_zero_e00626ca4948 (q : MvPolynomial (Fin 2 × Fin 2) F) (h : substZeroZeroZero q = 0) : X (0,0) ∣ q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineChowForm».«X_dvd_of_substZeroZeroZero_eq_zero» := P2M_GroundTheory_Heights__Heights_LineChowForm_X_dvd_of_substZeroZeroZero_eq_zero_e00626ca4948
