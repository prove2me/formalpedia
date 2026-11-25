-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionSmall_live_of_ne_76717d206e78
-- name    : P2M_GroundTheory_Heights__Heights_SectionSmall_live_of_ne_76717d206e78
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:20.007467+00:00
-- url     : https://prove2.me/theorems/37d1d9f8-a0be-475b-91e0-97c6acb2a04e
-- title:
--   P2 M Ground Theory Heights  Heights Section Small live of ne 76717d206e78: P2 M Ground Theory Heights  Heights Section Small live of ne 76717d206e78
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Small live of ne 76717d206e78 construction uses the P2 M Ground Theory Heights  Heights Section Small live of ne 76717d206e78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PSectionSmall.lean#L37-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PSectionSmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionSmall
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_SectionSmall_live_of_ne_76717d206e78 {P : ArithVariety n} {F : Type*} [CommRing F] {z : Cone n F} (hz : z ∈ P.points F)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionSmall».«live_of_ne» := P2M_GroundTheory_Heights__Heights_SectionSmall_live_of_ne_76717d206e78
