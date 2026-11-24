-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Raises_pow_f43fcada5b6c
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Raises_pow_f43fcada5b6c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:34.614316+00:00
-- url     : https://prove2.me/theorems/629dffac-9493-4d81-a9ee-fd115d490248
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower Raises pow f43fcada5b6c: P2 M Ground Theory Heights  Heights Effective HS Mul Tower Raises pow f43fcada5b6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower Raises pow f43fcada5b6c construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower Raises pow f43fcada5b6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L42-L48

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Raises_pow_f43fcada5b6c {τ : MulTower R A} {k : ℕ} {x : A} (hx : τ.Raises k x) (n : ℕ) :
    τ.Raises (k * n) (x ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«Raises».«pow» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Raises_pow_f43fcada5b6c
