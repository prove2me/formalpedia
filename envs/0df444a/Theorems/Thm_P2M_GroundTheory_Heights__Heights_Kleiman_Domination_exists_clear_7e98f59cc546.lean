-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_exists_clear_7e98f59cc546
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_exists_clear_7e98f59cc546
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:43.374276+00:00
-- url     : https://prove2.me/theorems/8fed4689-f2ad-4a34-988f-7fa96e751833
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination exists clear 7e98f59cc546: P2 M Ground Theory Heights  Heights Kleiman Domination exists clear 7e98f59cc546
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination exists clear 7e98f59cc546 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination exists clear 7e98f59cc546 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L268-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L268-L292

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_exists_clear_7e98f59cc546 {A : Subalgebra S Ω} {B : Submodule A Ω} (hB : B.FG) (P : Set Ω) (hP1 : (1 : Ω) ∈ P)
    (hPmul : ∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) (hPA : ∀ a ∈ P, a ∈ A)
    (h : ∀ g ∈ B, ∃ d ∈ P, d * g ∈ A) : ∃ d ∈ P, ∀ b ∈ B, d * b ∈ A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«exists_clear» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_exists_clear_7e98f59cc546
