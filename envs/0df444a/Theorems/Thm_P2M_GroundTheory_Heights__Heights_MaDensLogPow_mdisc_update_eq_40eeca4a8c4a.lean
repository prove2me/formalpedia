-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_update_eq_40eeca4a8c4a
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_update_eq_40eeca4a8c4a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:09.871567+00:00
-- url     : https://prove2.me/theorems/8f340472-8445-46cd-a201-6be3b6bf5650
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc update eq 40eeca4a8c4a: P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc update eq 40eeca4a8c4a
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc update eq 40eeca4a8c4a construction uses the P2 M Ground Theory Heights  Heights Ma Dens Log Pow mdisc update eq 40eeca4a8c4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L108-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L108-L129

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

theorem P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_update_eq_40eeca4a8c4a {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (i : Fin (n + 1 + 1))
    (hi : i ≠ 0) :
    mdisc (Function.update (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) i G) =
      mdisc (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLogPow».«mdisc_update_eq» := P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_update_eq_40eeca4a8c4a
