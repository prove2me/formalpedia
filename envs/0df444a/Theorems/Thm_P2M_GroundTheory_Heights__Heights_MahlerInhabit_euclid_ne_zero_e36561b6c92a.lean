-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_euclid_ne_zero_e36561b6c92a
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_euclid_ne_zero_e36561b6c92a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:48:30.19945+00:00
-- url     : https://prove2.me/theorems/fabb1f29-3d87-49f5-aacc-26f670272f36
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit euclid ne zero e36561b6c92a: P2 M Ground Theory Heights  Heights Mahler Inhabit euclid ne zero e36561b6c92a
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit euclid ne zero e36561b6c92a construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit euclid ne zero e36561b6c92a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L270-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L270-L273

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_euclid_ne_zero_e36561b6c92a : (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«euclid_ne_zero» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_euclid_ne_zero_e36561b6c92a
