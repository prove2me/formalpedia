-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_divCycle_2640b9484206
-- name    : P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_divCycle_2640b9484206
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:54.138714+00:00
-- url     : https://prove2.me/theorems/6e5ee4ee-86c0-4dc9-a0a4-82a3a4bba555
-- title:
--   P2 M Ground Theory Heights  Heights Slice Components mem support div Cycle 2640b9484206: P2 M Ground Theory Heights  Heights Slice Components mem support div Cycle 2640b9484206
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Components mem support div Cycle 2640b9484206 construction uses the P2 M Ground Theory Heights  Heights Slice Components mem support div Cycle 2640b9484206 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L77-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceComponents
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SliceComponents
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_divCycle_2640b9484206 {J W : Ideal (MvPolynomial (Fin n) F)} {u : Fin n → F} :
    W ∈ (divCycle J u).support ↔
      W ∈ relComps (J ⊔ Ideal.span {linForm u}) ∧ localMult (J ⊔ Ideal.span {linForm u}) W ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceComponents».«mem_support_divCycle» := P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_divCycle_2640b9484206
