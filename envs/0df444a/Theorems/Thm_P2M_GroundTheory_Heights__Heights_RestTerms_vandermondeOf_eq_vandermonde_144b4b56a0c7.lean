-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_eq_vandermonde_144b4b56a0c7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_eq_vandermonde_144b4b56a0c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:08.10186+00:00
-- url     : https://prove2.me/theorems/c1881ca7-98fe-4aac-9590-96ad071b84e1
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of eq vandermonde 144b4b56a0c7: P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of eq vandermonde 144b4b56a0c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of eq vandermonde 144b4b56a0c7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of eq vandermonde 144b4b56a0c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L42-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsPowerSumDecompositionHomogeneousComponent.lean#L42-L69

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_eq_vandermonde_144b4b56a0c7 {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    vandermondeOf v = GroundTheory.Heights₂.Heights.vandermonde v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«vandermondeOf_eq_vandermonde» := P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_eq_vandermonde_144b4b56a0c7
