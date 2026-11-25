-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_aeval_homog_512c9ab4a78a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_aeval_homog_512c9ab4a78a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:44.261229+00:00
-- url     : https://prove2.me/theorems/e1039bf1-9636-4e90-9892-247c8afd164f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates aeval homog 512c9ab4a78a: P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates aeval homog 512c9ab4a78a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates aeval homog 512c9ab4a78a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Birational Coordinates aeval homog 512c9ab4a78a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L52-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBirationalCoordinatesA.lean#L52-L69

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
omit hμ

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_aeval_homog_512c9ab4a78a {g : MRing (GlobalTheory κ)} {d : Unit → ℕ} (hg : IsMultiHomog g d) :
    aeval x g = μ ^ d () * j (aeval y g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BirationalCoordinates».«aeval_homog» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_aeval_homog_512c9ab4a78a
