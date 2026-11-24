-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_maximalIdeal_smul_top_lt_top_3d10a1377dbd
-- name    : P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_maximalIdeal_smul_top_lt_top_3d10a1377dbd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:47.702049+00:00
-- url     : https://prove2.me/theorems/4f414e3a-e4e8-4e81-a1e7-b400e070c95b
-- title:
--   P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower maximal Ideal smul top lt top 3d10a1377dbd: P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower maximal Ideal smul t
-- statement:
--   The P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower maximal Ideal smul top lt top 3d10a1377dbd construction uses the P2 M Ground Theory Heights  Heights Auslander Buchsbaum Depth Lower maximal Ideal smul top lt top 3d10a1377dbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumDepthLower.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAuslanderBuchsbaumDepthLower.lean#L25-L30

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

theorem P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_maximalIdeal_smul_top_lt_top_3d10a1377dbd (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AuslanderBuchsbaumDepthLower».«maximalIdeal_smul_top_lt_top» := P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_maximalIdeal_smul_top_lt_top_3d10a1377dbd
