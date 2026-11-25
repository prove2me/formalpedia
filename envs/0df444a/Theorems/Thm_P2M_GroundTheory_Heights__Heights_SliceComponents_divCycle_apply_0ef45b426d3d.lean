-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_divCycle_apply_0ef45b426d3d
-- name    : P2M_GroundTheory_Heights__Heights_SliceComponents_divCycle_apply_0ef45b426d3d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:52.925526+00:00
-- url     : https://prove2.me/theorems/16123b11-f247-40fc-83f7-22b319299dfe
-- title:
--   P2 M Ground Theory Heights  Heights Slice Components div Cycle apply 0ef45b426d3d: P2 M Ground Theory Heights  Heights Slice Components div Cycle apply 0ef45b426d3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Components div Cycle apply 0ef45b426d3d construction uses the P2 M Ground Theory Heights  Heights Slice Components div Cycle apply 0ef45b426d3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L84-L89

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

theorem P2M_GroundTheory_Heights__Heights_SliceComponents_divCycle_apply_0ef45b426d3d {J W : Ideal (MvPolynomial (Fin n) F)} {u : Fin n → F}
    (h : W ∈ relComps (J ⊔ Ideal.span {linForm u})) :
    divCycle J u W = localMult (J ⊔ Ideal.span {linForm u}) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceComponents».«divCycle_apply» := P2M_GroundTheory_Heights__Heights_SliceComponents_divCycle_apply_0ef45b426d3d
