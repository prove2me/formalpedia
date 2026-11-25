-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_iff_2bb896af3ee2
-- name    : P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_iff_2bb896af3ee2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:52.978327+00:00
-- url     : https://prove2.me/theorems/e23f822d-c31f-4e9b-83c5-83a624191704
-- title:
--   P2 M Ground Theory Heights  Heights Slice Components mem support iff 2bb896af3ee2: P2 M Ground Theory Heights  Heights Slice Components mem support iff 2bb896af3ee2
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Components mem support iff 2bb896af3ee2 construction uses the P2 M Ground Theory Heights  Heights Slice Components mem support iff 2bb896af3ee2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L104-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L104-L111

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

theorem P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_iff_2bb896af3ee2 {J W : Ideal (MvPolynomial (Fin n) F)} {u ℓ : Fin n → F}
    (hℓ : ∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) :
    W ∈ (divCycle J u).support ↔ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes ∧ linForm ℓ ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceComponents».«mem_support_iff» := P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_iff_2bb896af3ee2
