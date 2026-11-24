-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2
-- name    : P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:37.482059+00:00
-- url     : https://prove2.me/theorems/5a267a98-ae5c-4e7b-9665-64ef45e3f3e1
-- title:
--   P2 M Ground Theory Heights  Heights has Finite Mul Support i Sup place 6bf3c48ba8b2: P2 M Ground Theory Heights  Heights has Finite Mul Support i Sup place 6bf3c48ba8b2
-- statement:
--   The P2 M Ground Theory Heights  Heights has Finite Mul Support i Sup place 6bf3c48ba8b2 construction uses the P2 M Ground Theory Heights  Heights has Finite Mul Support i Sup place 6bf3c48ba8b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L59-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
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
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2 {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι]
    {y : ι → F} (hy : y ≠ 0) : Function.HasFiniteMulSupport fun w : FinitePlace F ↦ ⨆ i, w (y i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hasFiniteMulSupport_iSup_place» := P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2
