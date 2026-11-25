-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mem_chartLat_iff_b7234937320a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mem_chartLat_iff_b7234937320a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:38.33223+00:00
-- url     : https://prove2.me/theorems/248592ad-a7a9-5758-a117-c9bcb1a6aadc
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates mem chart Lat iff b7234937320a: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates mem chart Lat iff b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates mem chart Lat iff b7234937320a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates mem chart Lat iff b7234937320a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L82-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L82-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx
omit [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mem_chartLat_iff_b7234937320a (a : Unit → ℤ) (τ : ℕ) (s' : Ω'') :
    μ ^ ((τ : ℤ) * a ()) * j s' ∈ chartLat (ι := GlobalTheory κ) x a τ ↔ s' ∈ chartLat (ι := GlobalTheory κ) y a τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«mem_chartLat_iff» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mem_chartLat_iff_b7234937320a
