-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_nat_eq_of_ne_bot_of_le_ee963b0d7e7a
-- name    : P2M_GroundTheory_Heights__Heights_exists_nat_eq_of_ne_bot_of_le_ee963b0d7e7a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:53.956803+00:00
-- url     : https://prove2.me/theorems/10ec57fc-2092-52c2-bb85-b5d4ceeaa869
-- title:
--   P2 M Ground Theory Heights  Heights exists nat eq of ne bot of le ee963b0d7e7a: P2 M Ground Theory Heights  Heights exists nat eq of ne bot of le ee963b0d7e7a
-- statement:
--   The P2 M Ground Theory Heights  Heights exists nat eq of ne bot of le ee963b0d7e7a construction uses the P2 M Ground Theory Heights  Heights exists nat eq of ne bot of le ee963b0d7e7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L15-L22

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMProjDimCriterion
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
open IsLocalRing CategoryTheory RingTheory.Sequence

theorem P2M_GroundTheory_Heights__Heights_exists_nat_eq_of_ne_bot_of_le_ee963b0d7e7a {x : WithBot ℕ∞} {d : ℕ} (h0 : x ≠ ⊥) (hle : x ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, x = e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_nat_eq_of_ne_bot_of_le» := P2M_GroundTheory_Heights__Heights_exists_nat_eq_of_ne_bot_of_le_ee963b0d7e7a
