-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_isFundamentalDomain_of_isCompact_eb183c6717da
-- name    : P2M_GroundTheory_Heights__Theta_exists_isFundamentalDomain_of_isCompact_eb183c6717da
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:34.526518+00:00
-- url     : https://prove2.me/theorems/9ae8f864-f9a7-4c48-a802-0437292b192b
-- title:
--   P2 M Ground Theory Heights  Theta exists is Fundamental Domain of is Compact eb183c6717da: P2 M Ground Theory Heights  Theta exists is Fundamental Domain of is Compact eb183c6717da
-- statement:
--   The P2 M Ground Theory Heights  Theta exists is Fundamental Domain of is Compact eb183c6717da construction uses the P2 M Ground Theory Heights  Theta exists is Fundamental Domain of is Compact eb183c6717da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L105-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L105-L144

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

theorem P2M_GroundTheory_Heights__Theta_exists_isFundamentalDomain_of_isCompact_eb183c6717da [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {C : Set G} (hC : IsCompact C)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ C) :
    ∃ 𝓕 L : Set G, MeasurableSet 𝓕 ∧ IsCompact L ∧ 𝓕 ⊆ L ∧ ∀ x, ∃! γ : Γ, γ • x ∈ 𝓕 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«exists_isFundamentalDomain_of_isCompact» := P2M_GroundTheory_Heights__Theta_exists_isFundamentalDomain_of_isCompact_eb183c6717da
