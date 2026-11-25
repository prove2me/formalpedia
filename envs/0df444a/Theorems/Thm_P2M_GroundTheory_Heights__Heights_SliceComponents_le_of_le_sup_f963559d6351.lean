-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_le_of_le_sup_f963559d6351
-- name    : P2M_GroundTheory_Heights__Heights_SliceComponents_le_of_le_sup_f963559d6351
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:48.577832+00:00
-- url     : https://prove2.me/theorems/dd882c58-5cb5-5c97-a451-0c4f9355bbaf
-- title:
--   P2 M Ground Theory Heights  Heights Slice Components le of le sup f963559d6351: P2 M Ground Theory Heights  Heights Slice Components le of le sup f963559d6351
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Components le of le sup f963559d6351 construction uses the P2 M Ground Theory Heights  Heights Slice Components le of le sup f963559d6351 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceComponents.lean#L30-L35

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

theorem P2M_GroundTheory_Heights__Heights_SliceComponents_le_of_le_sup_f963559d6351 {V W : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F} (hV : IsHomogIdeal V)
    (hW : W.IsPrime) (hWh : IsHomogIdeal W) (ht : linForm t ∉ W) (h : V ≤ W ⊔ Ideal.span {linForm t - 1}) :
    V ≤ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceComponents».«le_of_le_sup» := P2M_GroundTheory_Heights__Heights_SliceComponents_le_of_le_sup_f963559d6351
