-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_one_b487892ad098
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_one_b487892ad098
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:14.297681+00:00
-- url     : https://prove2.me/theorems/f58edf25-2515-43e0-bce8-15498e0ef466
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises one b487892ad098: P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises one b487892ad098
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises one b487892ad098 construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises one b487892ad098 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L28-L30

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_one_b487892ad098 : τ.Raises 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«raises_one» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_one_b487892ad098
