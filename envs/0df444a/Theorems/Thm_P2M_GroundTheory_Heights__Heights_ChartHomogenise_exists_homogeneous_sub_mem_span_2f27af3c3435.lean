-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHomogenise_exists_homogeneous_sub_mem_span_2f27af3c3435
-- name    : P2M_GroundTheory_Heights__Heights_ChartHomogenise_exists_homogeneous_sub_mem_span_2f27af3c3435
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:03.904442+00:00
-- url     : https://prove2.me/theorems/503b7b74-7bd5-4288-9888-24b7cb36405f
-- title:
--   P2 M Ground Theory Heights  Heights Chart Homogenise exists homogeneous sub mem span 2f27af3c3435: P2 M Ground Theory Heights  Heights Chart Homogenise exists homogeneous sub mem span 2f27af3c3435
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Homogenise exists homogeneous sub mem span 2f27af3c3435 construction uses the P2 M Ground Theory Heights  Heights Chart Homogenise exists homogeneous sub mem span 2f27af3c3435 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartHomogenise.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartHomogenise.lean#L17-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
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
open GroundTheory.Heights₂.Heights.ChartHomogenise
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartHomogenise_exists_homogeneous_sub_mem_span_2f27af3c3435 (ℓ g : MvPolynomial (Fin n) F) (hℓ : ℓ.IsHomogeneous 1) :
    ∃ (G : MvPolynomial (Fin n) F) (D : ℕ), G.IsHomogeneous D ∧ G - g ∈ Ideal.span {ℓ - 1} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHomogenise».«exists_homogeneous_sub_mem_span» := P2M_GroundTheory_Heights__Heights_ChartHomogenise_exists_homogeneous_sub_mem_span_2f27af3c3435
