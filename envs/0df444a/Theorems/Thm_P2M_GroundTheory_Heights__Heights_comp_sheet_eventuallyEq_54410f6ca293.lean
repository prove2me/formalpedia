-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_comp_sheet_eventuallyEq_54410f6ca293
-- name    : P2M_GroundTheory_Heights__Heights_comp_sheet_eventuallyEq_54410f6ca293
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:31.574012+00:00
-- url     : https://prove2.me/theorems/7e149578-d2cc-4d3b-a75c-bf32f0eb14a6
-- title:
--   P2 M Ground Theory Heights  Heights comp sheet eventually Eq 54410f6ca293: P2 M Ground Theory Heights  Heights comp sheet eventually Eq 54410f6ca293
-- statement:
--   The P2 M Ground Theory Heights  Heights comp sheet eventually Eq 54410f6ca293 construction uses the P2 M Ground Theory Heights  Heights comp sheet eventually Eq 54410f6ca293 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L25-L30

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

theorem P2M_GroundTheory_Heights__Heights_comp_sheet_eventuallyEq_54410f6ca293 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (g : (Fin d → ℂ) → ℝ) :
    (fun w => g (A *ᵥ s w)) =ᶠ[𝓝 (A *ᵥ x)] g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«comp_sheet_eventuallyEq» := P2M_GroundTheory_Heights__Heights_comp_sheet_eventuallyEq_54410f6ca293
