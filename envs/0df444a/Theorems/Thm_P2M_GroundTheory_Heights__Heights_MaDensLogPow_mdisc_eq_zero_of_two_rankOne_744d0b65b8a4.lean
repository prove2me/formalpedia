-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_eq_zero_of_two_rankOne_744d0b65b8a4
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_eq_zero_of_two_rankOne_744d0b65b8a4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:49:09.93619+00:00
-- url     : https://prove2.me/theorems/c4dd0e5f-ae43-4159-af98-de4c43cbb60e
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc eq zero of two rank One 744d0b65b8a4: P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc eq zero of two rank One 744d0b65b8a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc eq zero of two rank One 744d0b65b8a4 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc eq zero of two rank One 744d0b65b8a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L30-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L30-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow
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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_eq_zero_of_two_rankOne_744d0b65b8a4 (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ)
    {a b : Fin D} (hab : a ≠ b) (x x' : Fin D → ℂ) (ha : A a = vecMulVec x w)
    (hb : A b = vecMulVec x' w) : mdisc A = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLogPow».«mdisc_eq_zero_of_two_rankOne» := P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_eq_zero_of_two_rankOne_744d0b65b8a4
