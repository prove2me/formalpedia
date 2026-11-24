-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_const_apply_5310b6bbe09d
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_const_apply_5310b6bbe09d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:19.294391+00:00
-- url     : https://prove2.me/theorems/93236c53-c89a-4e4d-90df-80d9c3bbcf2d
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Log Pow cons const apply 5310b6bbe09d: P2 M Ground Theory Heights  Heights Ma Dens Log Pow cons const apply 5310b6bbe09d
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Log Pow cons const apply 5310b6bbe09d construction uses the P2 M Ground Theory Heights  Heights Ma Dens Log Pow cons const apply 5310b6bbe09d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L90-L94

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

theorem P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_const_apply_5310b6bbe09d {n : ℕ} (A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (k : Fin (n + 1 + 1)) :
    (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) k = if k = 0 then A₀ else H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLogPow».«cons_const_apply» := P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_const_apply_5310b6bbe09d
