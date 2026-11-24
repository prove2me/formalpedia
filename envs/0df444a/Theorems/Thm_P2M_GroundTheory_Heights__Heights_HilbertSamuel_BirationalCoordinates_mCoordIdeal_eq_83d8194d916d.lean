-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mCoordIdeal_eq_83d8194d916d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mCoordIdeal_eq_83d8194d916d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:59.547654+00:00
-- url     : https://prove2.me/theorems/4f142efb-3e62-4d14-b2d4-497b8002065b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates m Coord Ideal eq 83d8194d916d: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates m Coord Ideal eq 83d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates m Coord Ideal eq 83d8194d916d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates m Coord Ideal eq 83d8194d916d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L21-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L21-L48

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mCoordIdeal_eq_83d8194d916d : mCoordIdeal (ι := GlobalTheory κ) y = mCoordIdeal (ι := GlobalTheory κ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«mCoordIdeal_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mCoordIdeal_eq_83d8194d916d
