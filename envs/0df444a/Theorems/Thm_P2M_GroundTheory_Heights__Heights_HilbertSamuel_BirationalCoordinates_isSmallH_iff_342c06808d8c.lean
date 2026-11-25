-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_isSmallH_iff_342c06808d8c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_isSmallH_iff_342c06808d8c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:00.316831+00:00
-- url     : https://prove2.me/theorems/1cf6a0cd-b026-5efc-aee4-b1762906e6f9
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates is Small H iff 342c06808d8c: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates is Small H iff 342c0680
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates is Small H iff 342c06808d8c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates is Small H iff 342c06808d8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L131-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L131-L137

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_isSmallH_iff_342c06808d8c (P : Ideal (MRing (GlobalTheory κ))) (A : HermLine (GlobalTheory κ)) (τ : ℕ) (s' : Ω'') :
    IsSmallH P x A τ (μ ^ ((τ : ℤ) * A.a ()) * j s') ↔ IsSmallH P y A τ s' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«isSmallH_iff» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_isSmallH_iff_342c06808d8c
