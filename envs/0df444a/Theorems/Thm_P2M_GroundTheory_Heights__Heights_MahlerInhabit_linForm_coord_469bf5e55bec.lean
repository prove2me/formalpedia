-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerInhabit_linForm_coord_469bf5e55bec
-- name    : P2M_GroundTheory_Heights__Heights_MahlerInhabit_linForm_coord_469bf5e55bec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:08.698217+00:00
-- url     : https://prove2.me/theorems/1823bef6-b8eb-426d-b375-f0a727dbfefc
-- title:
--   P2 M Ground Theory Heights  Heights Mahler Inhabit lin Form coord 469bf5e55bec: P2 M Ground Theory Heights  Heights Mahler Inhabit lin Form coord 469bf5e55bec
-- statement:
--   The P2 M Ground Theory Heights  Heights Mahler Inhabit lin Form coord 469bf5e55bec construction uses the P2 M Ground Theory Heights  Heights Mahler Inhabit lin Form coord 469bf5e55bec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L293-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L293-L294

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

theorem P2M_GroundTheory_Heights__Heights_MahlerInhabit_linForm_coord_469bf5e55bec (a : Fin 2) : linForm (coord a) = X a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MahlerInhabit».«linForm_coord» := P2M_GroundTheory_Heights__Heights_MahlerInhabit_linForm_coord_469bf5e55bec
