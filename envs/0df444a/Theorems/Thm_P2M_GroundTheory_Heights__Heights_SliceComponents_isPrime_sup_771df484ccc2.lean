-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_isPrime_sup_771df484ccc2
-- name    : P2M_GroundTheory_Heights__Heights_SliceComponents_isPrime_sup_771df484ccc2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:31.412821+00:00
-- url     : https://prove2.me/theorems/8babf08f-6216-44d2-a472-cc615d3fc5aa
-- title:
--   P2 M Ground Theory Heights  Heights Slice Components is Prime sup 771df484ccc2: P2 M Ground Theory Heights  Heights Slice Components is Prime sup 771df484ccc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Components is Prime sup 771df484ccc2 construction uses the P2 M Ground Theory Heights  Heights Slice Components is Prime sup 771df484ccc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L37-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L37-L75

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

theorem P2M_GroundTheory_Heights__Heights_SliceComponents_isPrime_sup_771df484ccc2 {W : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F} (hW : W.IsPrime)
    (hH : IsHomogIdeal W) (ht : linForm t ∉ W) : (W ⊔ Ideal.span {linForm t - 1}).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceComponents».«isPrime_sup» := P2M_GroundTheory_Heights__Heights_SliceComponents_isPrime_sup_771df484ccc2
