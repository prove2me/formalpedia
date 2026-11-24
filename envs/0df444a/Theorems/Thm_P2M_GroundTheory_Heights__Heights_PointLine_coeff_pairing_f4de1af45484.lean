-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_coeff_pairing_f4de1af45484
-- name    : P2M_GroundTheory_Heights__Heights_PointLine_coeff_pairing_f4de1af45484
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:45.91378+00:00
-- url     : https://prove2.me/theorems/76eef61e-b2b7-4204-b2b2-431a531f3182
-- title:
--   P2 M Ground Theory Heights  Heights Point Line coeff pairing f4de1af45484: P2 M Ground Theory Heights  Heights Point Line coeff pairing f4de1af45484
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Line coeff pairing f4de1af45484 construction uses the P2 M Ground Theory Heights  Heights Point Line coeff pairing f4de1af45484 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPointLine.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
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
open GroundTheory.Heights₂.Heights.PointLine
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointLine_coeff_pairing_f4de1af45484 (y : Fin n → ℂ) (j : Fin n) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (pairing y) = y j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointLine».«coeff_pairing» := P2M_GroundTheory_Heights__Heights_PointLine_coeff_pairing_f4de1af45484
