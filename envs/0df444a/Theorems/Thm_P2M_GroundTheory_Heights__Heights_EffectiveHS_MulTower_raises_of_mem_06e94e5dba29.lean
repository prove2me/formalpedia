-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_of_mem_06e94e5dba29
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_of_mem_06e94e5dba29
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:09.23625+00:00
-- url     : https://prove2.me/theorems/f93d655f-af08-473b-8723-c00a196c6ba7
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises of mem 06e94e5dba29: P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises of mem 06e94e5dba29
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises of mem 06e94e5dba29 construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises of mem 06e94e5dba29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L32-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_of_mem_06e94e5dba29 {w : A} (hw : w ∈ τ.W) : τ.Raises 1 w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«raises_of_mem» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_of_mem_06e94e5dba29
