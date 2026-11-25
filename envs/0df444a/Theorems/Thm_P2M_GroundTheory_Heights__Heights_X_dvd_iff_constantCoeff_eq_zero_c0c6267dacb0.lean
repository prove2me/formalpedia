-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_dvd_iff_constantCoeff_eq_zero_c0c6267dacb0
-- name    : P2M_GroundTheory_Heights__Heights_X_dvd_iff_constantCoeff_eq_zero_c0c6267dacb0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:57.043797+00:00
-- url     : https://prove2.me/theorems/402de71d-796e-5a6f-a5de-81beb71d2764
-- title:
--   P2 M Ground Theory Heights  Heights X dvd iff constant Coeff eq zero c0c6267dacb0: P2 M Ground Theory Heights  Heights X dvd iff constant Coeff eq zero c0c6267dacb0
-- statement:
--   The P2 M Ground Theory Heights  Heights X dvd iff constant Coeff eq zero c0c6267dacb0 construction uses the P2 M Ground Theory Heights  Heights X dvd iff constant Coeff eq zero c0c6267dacb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L271-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L271-L291

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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

theorem P2M_GroundTheory_Heights__Heights_X_dvd_iff_constantCoeff_eq_zero_c0c6267dacb0 {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 1 × Fin 1) R) : X (0, 0) ∣ f ↔ constantCoeff f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«X_dvd_iff_constantCoeff_eq_zero» := P2M_GroundTheory_Heights__Heights_X_dvd_iff_constantCoeff_eq_zero_c0c6267dacb0
