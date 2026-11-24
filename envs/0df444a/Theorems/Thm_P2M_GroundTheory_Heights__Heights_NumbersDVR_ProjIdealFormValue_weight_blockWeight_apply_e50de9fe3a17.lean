-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_weight_blockWeight_apply_e50de9fe3a17
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_weight_blockWeight_apply_e50de9fe3a17
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:38:01.490934+00:00
-- url     : https://prove2.me/theorems/c7e15d5f-b16a-43cd-83dc-8ee9d0331cff
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Proj Ideal Form Value weight block Weight apply e50de9fe3a17: P2 M Ground Theory Heights  Heights Numbers DVR Proj Ideal Form Value weight block Weight
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Proj Ideal Form Value weight block Weight apply e50de9fe3a17 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Proj Ideal Form Value weight block Weight apply e50de9fe3a17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PProjIdealFormValue.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PProjIdealFormValue.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ProjIdealFormValue

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_weight_blockWeight_apply_e50de9fe3a17 {K : Type*} [DecidableEq K] {ι : K → Type*} (m : (Σ k, ι k) →₀ ℕ)
    (k : K) : Finsupp.weight (blockWeight ι) m k = Finsupp.mapDomain Sigma.fst m k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ProjIdealFormValue».«weight_blockWeight_apply» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_weight_blockWeight_apply_e50de9fe3a17
