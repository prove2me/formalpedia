-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_isOpen_small_b5c2f2fc479e
-- name    : P2M_GroundTheory_Heights__Theta_exists_isOpen_small_b5c2f2fc479e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:43.737633+00:00
-- url     : https://prove2.me/theorems/d9702ed0-196b-4ccc-9dd0-099233bfb616
-- title:
--   P2 M Ground Theory Heights  Theta exists is Open small b5c2f2fc479e: P2 M Ground Theory Heights  Theta exists is Open small b5c2f2fc479e
-- statement:
--   The P2 M Ground Theory Heights  Theta exists is Open small b5c2f2fc479e construction uses the P2 M Ground Theory Heights  Theta exists is Open small b5c2f2fc479e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L25-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L25-L39

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

theorem P2M_GroundTheory_Heights__Theta_exists_isOpen_small_b5c2f2fc479e (Γ : Subgroup G) [DiscreteTopology Γ] (c : G) :
    ∃ V : Set G, IsOpen V ∧ c ∈ V ∧ (∃ L, IsCompact L ∧ V ⊆ L) ∧
      ∀ γ ∈ Γ, ∀ x ∈ V, γ * x ∈ V → γ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«exists_isOpen_small» := P2M_GroundTheory_Heights__Theta_exists_isOpen_small_b5c2f2fc479e
