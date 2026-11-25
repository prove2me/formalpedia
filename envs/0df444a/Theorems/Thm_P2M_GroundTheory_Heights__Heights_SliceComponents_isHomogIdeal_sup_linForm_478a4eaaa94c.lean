-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_isHomogIdeal_sup_linForm_478a4eaaa94c
-- name    : P2M_GroundTheory_Heights__Heights_SliceComponents_isHomogIdeal_sup_linForm_478a4eaaa94c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:25.730057+00:00
-- url     : https://prove2.me/theorems/3fc8d06a-5fab-59e0-b5f8-3011cf0afa92
-- title:
--   P2 M Ground Theory Heights  Heights Slice Components is Homog Ideal sup lin Form 478a4eaaa94c: P2 M Ground Theory Heights  Heights Slice Components is Homog Ideal sup lin Form 478a4eaaa94c
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Components is Homog Ideal sup lin Form 478a4eaaa94c construction uses the P2 M Ground Theory Heights  Heights Slice Components is Homog Ideal sup lin Form 478a4eaaa94c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L23-L28

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

theorem P2M_GroundTheory_Heights__Heights_SliceComponents_isHomogIdeal_sup_linForm_478a4eaaa94c {J : Ideal (MvPolynomial (Fin n) F)} (hJ : IsHomogIdeal J) (u : Fin n → F) :
    IsHomogIdeal (J ⊔ Ideal.span {linForm u}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceComponents».«isHomogIdeal_sup_linForm» := P2M_GroundTheory_Heights__Heights_SliceComponents_isHomogIdeal_sup_linForm_478a4eaaa94c
