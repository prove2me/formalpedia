-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_2ebb31936f55
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_2ebb31936f55
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:16.110605+00:00
-- url     : https://prove2.me/theorems/7d5fcc3d-05fb-4729-b351-bb47861b52d5
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises prod 2ebb31936f55: P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises prod 2ebb31936f55
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises prod 2ebb31936f55 construction uses the P2 M Ground Theory Heights  Heights Effective HS Mul Tower raises prod 2ebb31936f55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L50-L57

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

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_2ebb31936f55 {ι : Type*} (t : Finset ι) (k : ι → ℕ) (x : ι → A)
    (h : ∀ i ∈ t, τ.Raises (k i) (x i)) : τ.Raises (∑ i ∈ t, k i) (∏ i ∈ t, x i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«MulTower».«raises_prod» := P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_2ebb31936f55
