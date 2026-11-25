-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_smallSectionCount_eq_of_birational_d8b403abde42
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_smallSectionCount_eq_of_birational_d8b403abde42
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:30.851093+00:00
-- url     : https://prove2.me/theorems/dbed7c78-67ed-422f-beff-c5a0658bd3f2
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates small Section Count eq of birational d8b403abde42: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates s
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates small Section Count eq of birational d8b403abde42 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates small Section Count eq of birational d8b403abde42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L139-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L139-L157

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_smallSectionCount_eq_of_birational_d8b403abde42 {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (A : HermLine (GlobalTheory κ)) (τ : ℕ) :
    smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) y) y A) (chartLat (ι := GlobalTheory κ) y A.a) τ =
      smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x) x A) (chartLat (ι := GlobalTheory κ) x A.a) τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«smallSectionCount_eq_of_birational» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_smallSectionCount_eq_of_birational_d8b403abde42
