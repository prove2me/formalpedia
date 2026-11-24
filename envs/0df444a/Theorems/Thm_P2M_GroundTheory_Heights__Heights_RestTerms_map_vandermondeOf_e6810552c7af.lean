-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_map_vandermondeOf_e6810552c7af
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_map_vandermondeOf_e6810552c7af
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:52.837054+00:00
-- url     : https://prove2.me/theorems/4cbc84cd-1e7e-4645-8c0c-2b116c4f774e
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms map vandermonde Of e6810552c7af: P2 M Ground Theory Heights  Heights Rest Terms map vandermonde Of e6810552c7af
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms map vandermonde Of e6810552c7af construction uses the P2 M Ground Theory Heights  Heights Rest Terms map vandermonde Of e6810552c7af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L38-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_map_vandermondeOf_e6810552c7af {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (vandermondeOf v) = vandermondeOf (fun i => φ (v i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«map_vandermondeOf» := P2M_GroundTheory_Heights__Heights_RestTerms_map_vandermondeOf_e6810552c7af
