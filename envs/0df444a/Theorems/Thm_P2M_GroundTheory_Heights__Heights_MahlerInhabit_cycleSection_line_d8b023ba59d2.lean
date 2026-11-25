-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_cycleSection_line_d8b023ba59d2
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_cycleSection_line_d8b023ba59d2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:27.714789+00:00
-- url     : https://prove2.me/theorems/465aa94b-b070-4c8d-aee0-e9fa251de32c
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit cycle Section line d8b023ba59d2: P2 M Ground Theory Heights  Heights Mahler Inhabit cycle Section line d8b023ba59d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit cycle Section line d8b023ba59d2 construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit cycle Section line d8b023ba59d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L296-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L296-L298

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_cycleSection_line_d8b023ba59d2 (u : Fin 2 → ℂ) :
    cycleSection (Finsupp.single (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) 1) u = divCycle ⊥ u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«cycleSection_line» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_cycleSection_line_d8b023ba59d2
