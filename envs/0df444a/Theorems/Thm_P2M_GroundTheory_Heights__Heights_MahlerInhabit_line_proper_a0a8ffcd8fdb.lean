-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_proper_a0a8ffcd8fdb
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_proper_a0a8ffcd8fdb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:22.24556+00:00
-- url     : https://prove2.me/theorems/d34a628f-9c1b-4723-a0ed-1a07516f0b18
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit line proper a0a8ffcd8fdb: P2 M Ground Theory Heights  Heights Mahler Inhabit line proper a0a8ffcd8fdb
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit line proper a0a8ffcd8fdb construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit line proper a0a8ffcd8fdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L300-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L300-L317

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_proper_a0a8ffcd8fdb (a b : Fin 2) (hab : a ≠ b) :
    IsAdmissible (divCycle (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (coord a)) (coord b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«line_proper» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_line_proper_a0a8ffcd8fdb
