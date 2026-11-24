-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_chartPow_ne_zero_0ca6bf248649
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_chartPow_ne_zero_0ca6bf248649
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:09.024156+00:00
-- url     : https://prove2.me/theorems/b5bba8a7-2036-4c6e-8297-aca99b6cd8e9
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data chart Pow ne zero 0ca6bf248649: P2 M Ground Theory Heights  Heights Add Block Data chart Pow ne zero 0ca6bf248649
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data chart Pow ne zero 0ca6bf248649 construction uses the P2 M Ground Theory Heights  Heights Add Block Data chart Pow ne zero 0ca6bf248649 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartPowNeZero.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartPowNeZero.lean#L15-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartPowNeZero
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
open GroundTheory.Heights₂.Heights.AddBlockData
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_chartPow_ne_zero_0ca6bf248649 {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (a : ι → ℤ) :
    P.chartPow c a ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«chartPow_ne_zero» := P2M_GroundTheory_Heights__Heights_AddBlockData_chartPow_ne_zero_0ca6bf248649
