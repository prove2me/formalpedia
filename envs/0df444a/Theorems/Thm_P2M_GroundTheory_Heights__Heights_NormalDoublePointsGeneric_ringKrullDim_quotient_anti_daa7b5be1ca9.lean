-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_anti_daa7b5be1ca9
-- name    : P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_anti_daa7b5be1ca9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:10.477882+00:00
-- url     : https://prove2.me/theorems/263e5b5d-4f8c-5df8-975b-4d4fec7c5bca
-- title:
--   P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quotient anti daa7b5be1ca9: P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quotient ant
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quotient anti daa7b5be1ca9 construction uses the P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quotient anti daa7b5be1ca9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L27-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric
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
open MvPolynomial Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric

theorem P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_anti_daa7b5be1ca9 {R : Type*} [CommRing R] {K K' : Ideal R} (h : K ≤ K') :
    ringKrullDim (R ⧸ K') ≤ ringKrullDim (R ⧸ K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalDoublePointsGeneric».«ringKrullDim_quotient_anti» := P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_anti_daa7b5be1ca9
