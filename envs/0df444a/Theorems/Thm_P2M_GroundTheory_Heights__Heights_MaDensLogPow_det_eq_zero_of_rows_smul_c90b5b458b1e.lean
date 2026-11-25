-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_det_eq_zero_of_rows_smul_c90b5b458b1e
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLogPow_det_eq_zero_of_rows_smul_c90b5b458b1e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:49:45.56153+00:00
-- url     : https://prove2.me/theorems/9a7e1a11-7c99-41db-a7bf-ebd0129a25d6
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Log Pow det eq zero of rows smul c90b5b458b1e: P2 M Ground Theory Heights  Heights Ma Dens Log Pow det eq zero of rows smul c90b5b458b1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Log Pow det eq zero of rows smul c90b5b458b1e construction uses the P2 M Ground Theory Heights  Heights Ma Dens Log Pow det eq zero of rows smul c90b5b458b1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L19-L28

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

theorem P2M_GroundTheory_Heights__Heights_MaDensLogPow_det_eq_zero_of_rows_smul_c90b5b458b1e (M : Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ) {i j : Fin D}
    (hij : i ≠ j) (a b : ℂ) (hi : M i = a • w) (hj : M j = b • w) : M.det = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLogPow».«det_eq_zero_of_rows_smul» := P2M_GroundTheory_Heights__Heights_MaDensLogPow_det_eq_zero_of_rows_smul_c90b5b458b1e
