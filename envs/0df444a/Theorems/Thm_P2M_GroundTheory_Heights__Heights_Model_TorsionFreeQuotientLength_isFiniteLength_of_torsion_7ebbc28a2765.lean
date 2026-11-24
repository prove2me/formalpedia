-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_isFiniteLength_of_torsion_7ebbc28a2765
-- name    : P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_isFiniteLength_of_torsion_7ebbc28a2765
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:19.840199+00:00
-- url     : https://prove2.me/theorems/6d6334b2-bac7-48c4-96d1-9129e7607e02
-- title:
--   P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length is Finite Length of torsion 7ebbc28a2765: P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length is Finite Length
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length is Finite Length of torsion 7ebbc28a2765 construction uses the P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length is Finite Length of torsion 7ebbc28a2765 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PTorsionFreeQuotientLength.lean#L43-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PTorsionFreeQuotientLength.lean#L43-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_isFiniteLength_of_torsion_7ebbc28a2765 [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (Q : Type*) [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (hQ : ∀ q : Q, ∃ c : R, c ≠ 0 ∧ c • q = 0) : IsFiniteLength R Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«TorsionFreeQuotientLength».«isFiniteLength_of_torsion» := P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_isFiniteLength_of_torsion_7ebbc28a2765
