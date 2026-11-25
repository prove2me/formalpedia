-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_existsUnique_mem_firstHit_2887f9ddb304
-- name    : P2M_GroundTheory_Heights__Theta_existsUnique_mem_firstHit_2887f9ddb304
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:32.945815+00:00
-- url     : https://prove2.me/theorems/18b2063f-caed-472c-8ed4-fafb56048623
-- title:
--   P2 M Ground Theory Heights  Theta exists Unique mem first Hit 2887f9ddb304: P2 M Ground Theory Heights  Theta exists Unique mem first Hit 2887f9ddb304
-- statement:
--   The P2 M Ground Theory Heights  Theta exists Unique mem first Hit 2887f9ddb304 construction uses the P2 M Ground Theory Heights  Theta exists Unique mem first Hit 2887f9ddb304 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L57-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L57-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]

theorem P2M_GroundTheory_Heights__Theta_existsUnique_mem_firstHit_2887f9ddb304 (Γ : Subgroup G) (A : ℕ → Set G)
    (hinj : ∀ i, ∀ γ ∈ Γ, ∀ x ∈ A i, γ * x ∈ A i → γ = 1)
    (hcov : ∀ x : G, ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i) (x : G) :
    ∃! γ : Γ, γ • x ∈ firstHit Γ A := by sorry

alias «GroundTheory».«Heights₂».«Theta».«existsUnique_mem_firstHit» := P2M_GroundTheory_Heights__Theta_existsUnique_mem_firstHit_2887f9ddb304
