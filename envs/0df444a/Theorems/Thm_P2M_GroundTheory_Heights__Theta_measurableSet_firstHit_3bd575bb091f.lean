-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_measurableSet_firstHit_3bd575bb091f
-- name    : P2M_GroundTheory_Heights__Theta_measurableSet_firstHit_3bd575bb091f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:44.966477+00:00
-- url     : https://prove2.me/theorems/0a50faac-c518-5a68-99a9-c1bf11e57022
-- title:
--   P2 M Ground Theory Heights  Theta measurable Set first Hit 3bd575bb091f: P2 M Ground Theory Heights  Theta measurable Set first Hit 3bd575bb091f
-- statement:
--   The P2 M Ground Theory Heights  Theta measurable Set first Hit 3bd575bb091f construction uses the P2 M Ground Theory Heights  Theta measurable Set first Hit 3bd575bb091f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean#L52-L55

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

theorem P2M_GroundTheory_Heights__Theta_measurableSet_firstHit_3bd575bb091f [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    {A : ℕ → Set G} (hA : ∀ i, IsOpen (A i)) : MeasurableSet (firstHit Γ A) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«measurableSet_firstHit» := P2M_GroundTheory_Heights__Theta_measurableSet_firstHit_3bd575bb091f
