-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_cons_const_apply_6e8bc6b37f22
-- name    : P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_cons_const_apply_6e8bc6b37f22
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:57:08.379821+00:00
-- url     : https://prove2.me/theorems/9dfa6141-1630-4bb2-af16-ccf50801a56e
-- title:
--   P2 M Ground Theory Heights  Heights Ma Dens Log Pow cons cons const apply 6e8bc6b37f22: P2 M Ground Theory Heights  Heights Ma Dens Log Pow cons cons const apply 6e8bc6b37f22
-- statement:
--   The P2 M Ground Theory Heights  Heights Ma Dens Log Pow cons cons const apply 6e8bc6b37f22 construction uses the P2 M Ground Theory Heights  Heights Ma Dens Log Pow cons cons const apply 6e8bc6b37f22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L96-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaDensLogPow.lean#L96-L106

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

theorem P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_cons_const_apply_6e8bc6b37f22 {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (k : Fin (n + 1 + 1)) :
    (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) k =
      if k = 0 then G else if k = 1 then A₀ else H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MaDensLogPow».«cons_cons_const_apply» := P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_cons_const_apply_6e8bc6b37f22
