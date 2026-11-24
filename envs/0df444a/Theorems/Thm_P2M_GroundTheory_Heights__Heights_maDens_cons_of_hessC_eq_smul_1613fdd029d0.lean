-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_maDens_cons_of_hessC_eq_smul_1613fdd029d0
-- name    : P2M_GroundTheory_Heights__Heights_maDens_cons_of_hessC_eq_smul_1613fdd029d0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:16.008182+00:00
-- url     : https://prove2.me/theorems/ecbd8513-3c5c-473c-89d2-400773f0d751
-- title:
--   P2 M Ground Theory Heights  Heights ma Dens cons of hess C eq smul 1613fdd029d0: P2 M Ground Theory Heights  Heights ma Dens cons of hess C eq smul 1613fdd029d0
-- statement:
--   The P2 M Ground Theory Heights  Heights ma Dens cons of hess C eq smul 1613fdd029d0 construction uses the P2 M Ground Theory Heights  Heights ma Dens cons of hess C eq smul 1613fdd029d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffGradient.lean#L32-L46

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

theorem P2M_GroundTheory_Heights__Heights_maDens_cons_of_hessC_eq_smul_1613fdd029d0 {D : ℕ} (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) (c : ℝ)
    (h : hessC f y = (c : ℂ) • hessC g y) :
    maDens (Fin.cons f ψ) y = c * maDens (Fin.cons g ψ) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«maDens_cons_of_hessC_eq_smul» := P2M_GroundTheory_Heights__Heights_maDens_cons_of_hessC_eq_smul_1613fdd029d0
