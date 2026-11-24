-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_support_residueModule_5535d1c543f8
-- name    : P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_support_residueModule_5535d1c543f8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:49.92573+00:00
-- url     : https://prove2.me/theorems/f9ce9f5a-7871-4b78-a1ed-ccc55cce5bac
-- title:
--   P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower support residue Module 5535d1c543f8: P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower support residue Module 5535
-- statement:
--   The P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower support residue Module 5535d1c543f8 construction uses the P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower support residue Module 5535d1c543f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumDepthLower.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumDepthLower.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumDepthLower
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
open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence
universe u
open GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_support_residueModule_5535d1c543f8 :
    Module.support R (residueModule R) = PrimeSpectrum.zeroLocus (maximalIdeal R) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AuslanderBuchsbaumDepthLower».«support_residueModule» := P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_support_residueModule_5535d1c543f8
