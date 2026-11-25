-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_birational_ratios_c3761376fe95
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_birational_ratios_c3761376fe95
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:22.562331+00:00
-- url     : https://prove2.me/theorems/159694e6-f6fe-43fe-84f0-cc1f025e78aa
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates birational ratios c3761376fe95: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates birational ratios c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates birational ratios c3761376fe95 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates birational ratios c3761376fe95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinates.lean#L33-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinates.lean#L33-L99

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_birational_ratios_c3761376fe95 (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) :
    Birational (ι := GlobalTheory κ) (ratios x c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«birational_ratios» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_birational_ratios_c3761376fe95
