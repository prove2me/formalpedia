-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_chartRingZ_eq_335699c6df6a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_chartRingZ_eq_335699c6df6a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:13.929946+00:00
-- url     : https://prove2.me/theorems/f75dfcd4-3a06-4702-af97-244c3fbb9af9
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates chart Ring Z eq 335699c6df6a: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates chart Ring Z eq 335699
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates chart Ring Z eq 335699c6df6a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates chart Ring Z eq 335699c6df6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L73-L78

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_chartRingZ_eq_335699c6df6a (c' : Unit → κ) :
    chartRingZ (ι := GlobalTheory κ) x c' = (chartRingZ (ι := GlobalTheory κ) y c').map j.toIntAlgHom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«chartRingZ_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_chartRingZ_eq_335699c6df6a
