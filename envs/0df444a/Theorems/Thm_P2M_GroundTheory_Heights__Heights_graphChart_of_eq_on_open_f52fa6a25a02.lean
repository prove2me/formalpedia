-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_graphChart_of_eq_on_open_f52fa6a25a02
-- name    : P2M_GroundTheory_Heights__Heights_graphChart_of_eq_on_open_f52fa6a25a02
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:46.038203+00:00
-- url     : https://prove2.me/theorems/055026e2-3b38-4417-8b31-13a40981db84
-- title:
--   P2 M Ground Theory Heights  Heights graph Chart of eq on open f52fa6a25a02: P2 M Ground Theory Heights  Heights graph Chart of eq on open f52fa6a25a02
-- statement:
--   The P2 M Ground Theory Heights  Heights graph Chart of eq on open f52fa6a25a02 construction uses the P2 M Ground Theory Heights  Heights graph Chart of eq on open f52fa6a25a02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RingKrullDimQuotientMinimalPrimeAddOne.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RingKrullDimQuotientMinimalPrimeAddOne.lean#L14-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularOffHypersurface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotientMinimalPrimeAddOne
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
open MvPolynomial Filter Topology ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_graphChart_of_eq_on_open_f52fa6a25a02 {n d : ℕ} {Y Y' U : Set (Fin n → ℂ)} {q : Fin n → ℂ}
    (hU : IsOpen U) (hqU : q ∈ U) (hYU : Y' ∩ U = Y ∩ U)
    (h : ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) :
    ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y' ∩ V = g '' O := by sorry

alias «GroundTheory».«Heights₂».«Heights».«graphChart_of_eq_on_open» := P2M_GroundTheory_Heights__Heights_graphChart_of_eq_on_open_f52fa6a25a02
