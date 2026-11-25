-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_spanFinrank_maximalIdeal_le_quotient_of_le_sq_c23dc5f32007
-- name    : P2M_GroundTheory_Heights__Heights_spanFinrank_maximalIdeal_le_quotient_of_le_sq_c23dc5f32007
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:26.863317+00:00
-- url     : https://prove2.me/theorems/958c51bb-366e-4198-a44e-9431bcc100ad
-- title:
--   P2 M Ground Theory Heights  Heights span Finrank maximal Ideal le quotient of le sq c23dc5f32007: P2 M Ground Theory Heights  Heights span Finrank maximal Ideal le quotient of le sq c23dc5f32007
-- statement:
--   The P2 M Ground Theory Heights  Heights span Finrank maximal Ideal le quotient of le sq c23dc5f32007 construction uses the P2 M Ground Theory Heights  Heights span Finrank maximal Ideal le quotient of le sq c23dc5f32007 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RegularQuotientGenerators.lean#L11-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RegularQuotientGenerators.lean#L11-L48

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularQuotientGenerators
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
open IsLocalRing Ideal
universe u

theorem P2M_GroundTheory_Heights__Heights_spanFinrank_maximalIdeal_le_quotient_of_le_sq_c23dc5f32007 {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ I)] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ I)).spanFinrank := by sorry

alias «GroundTheory».«Heights₂».«Heights».«spanFinrank_maximalIdeal_le_quotient_of_le_sq» := P2M_GroundTheory_Heights__Heights_spanFinrank_maximalIdeal_le_quotient_of_le_sq_c23dc5f32007
