-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_eq_mul_ratios_73d28504c04b
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_eq_mul_ratios_73d28504c04b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:16.95785+00:00
-- url     : https://prove2.me/theorems/4bc676ba-35f1-4ded-96f3-3b764719b098
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates eq mul ratios 73d28504c04b: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates eq mul ratios 73d28504c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates eq mul ratios 73d28504c04b construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates eq mul ratios 73d28504c04b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinates.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinates.lean#L28-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinates
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
variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]
omit [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_eq_mul_ratios_73d28504c04b (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (p : Ix κ) :
    x p = x ⟨(), c⟩ * (ratioField x c).subtype (ratios x c p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«eq_mul_ratios» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_eq_mul_ratios_73d28504c04b
