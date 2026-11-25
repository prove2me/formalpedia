-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_localMult_ne_zero_13f8534e8d73
-- name    : P2M_GroundTheory_Heights__Heights_SliceComponents_localMult_ne_zero_13f8534e8d73
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:41.297059+00:00
-- url     : https://prove2.me/theorems/04782bde-c991-4551-9eef-3e02f24b78d6
-- title:
--   P2 M Ground Theory Heights  Heights Slice Components local Mult ne zero 13f8534e8d73: P2 M Ground Theory Heights  Heights Slice Components local Mult ne zero 13f8534e8d73
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Components local Mult ne zero 13f8534e8d73 construction uses the P2 M Ground Theory Heights  Heights Slice Components local Mult ne zero 13f8534e8d73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L91-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L91-L102

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

theorem P2M_GroundTheory_Heights__Heights_SliceComponents_localMult_ne_zero_13f8534e8d73 {A : Type} [CommRing A] [IsNoetherianRing A] {J W : Ideal A} {x : A}
    (hW : W ∈ (J ⊔ Ideal.span {x}).minimalPrimes) : localMult (J ⊔ Ideal.span {x}) W ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceComponents».«localMult_ne_zero» := P2M_GroundTheory_Heights__Heights_SliceComponents_localMult_ne_zero_13f8534e8d73
