-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_exists_of_mem_chartLat_a77184435530
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_exists_of_mem_chartLat_a77184435530
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:04.476284+00:00
-- url     : https://prove2.me/theorems/7fdb6b79-f523-41a4-a3dc-6d275d2d9ebc
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates exists of mem chart Lat a77184435530: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates exists of mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates exists of mem chart Lat a77184435530 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates exists of mem chart Lat a77184435530 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L103-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L103-L118

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_exists_of_mem_chartLat_a77184435530 {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (a : Unit → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ chartLat (ι := GlobalTheory κ) x a τ) : ∃ s' : Ω'', μ ^ ((τ : ℤ) * a ()) * j s' = s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«exists_of_mem_chartLat» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_exists_of_mem_chartLat_a77184435530
