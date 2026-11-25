-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_ratios_c_873ba0532ef9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_ratios_c_873ba0532ef9
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:36.248655+00:00
-- url     : https://prove2.me/theorems/f0d41f02-0b38-4209-b836-7cf2721b8184
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates ratios c 873ba0532ef9: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates ratios c 873ba0532ef9
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates ratios c 873ba0532ef9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates ratios c 873ba0532ef9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinates.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinates.lean#L24-L25

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_ratios_c_873ba0532ef9 (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) : ratios x c ⟨(), c⟩ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«ratios_c» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_ratios_c_873ba0532ef9
