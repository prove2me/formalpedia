-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sheetSum_le_mul_0df1d0f6a4b5
-- name    : P2M_GroundTheory_Heights__Heights_sheetSum_le_mul_0df1d0f6a4b5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:36.016574+00:00
-- url     : https://prove2.me/theorems/92c737f6-7c5c-4006-ad7f-c7d57f9a0e78
-- title:
--   P2 M Ground Theory Heights  Heights sheet Sum le mul 0df1d0f6a4b5: P2 M Ground Theory Heights  Heights sheet Sum le mul 0df1d0f6a4b5
-- statement:
--   The P2 M Ground Theory Heights  Heights sheet Sum le mul 0df1d0f6a4b5 construction uses the P2 M Ground Theory Heights  Heights sheet Sum le mul 0df1d0f6a4b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L53-L65

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

theorem P2M_GroundTheory_Heights__Heights_sheetSum_le_mul_0df1d0f6a4b5 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) (c : ℝ)
    (F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (h : ∀ x ∈ fibre J A y, ∀ s, IsSheetAt J A x s → F x s ≤ c * G x s) :
    sheetSum J A F y ≤ c * sheetSum J A G y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sheetSum_le_mul» := P2M_GroundTheory_Heights__Heights_sheetSum_le_mul_0df1d0f6a4b5
