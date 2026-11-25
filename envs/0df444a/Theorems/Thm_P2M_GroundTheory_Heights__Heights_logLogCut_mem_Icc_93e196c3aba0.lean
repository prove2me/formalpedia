-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogCut_mem_Icc_93e196c3aba0
-- name    : P2M_GroundTheory_Heights__Heights_logLogCut_mem_Icc_93e196c3aba0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:05.731093+00:00
-- url     : https://prove2.me/theorems/486b959e-4804-42d9-8fa1-76c7c2236f78
-- title:
--   P2 M Ground Theory Heights  Heights log Log Cut mem Icc 93e196c3aba0: P2 M Ground Theory Heights  Heights log Log Cut mem Icc 93e196c3aba0
-- statement:
--   The P2 M Ground Theory Heights  Heights log Log Cut mem Icc 93e196c3aba0 construction uses the P2 M Ground Theory Heights  Heights log Log Cut mem Icc 93e196c3aba0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCutHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
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
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_logLogCut_mem_Icc_93e196c3aba0 {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) :
    logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logLogCut_mem_Icc» := P2M_GroundTheory_Heights__Heights_logLogCut_mem_Icc_93e196c3aba0
