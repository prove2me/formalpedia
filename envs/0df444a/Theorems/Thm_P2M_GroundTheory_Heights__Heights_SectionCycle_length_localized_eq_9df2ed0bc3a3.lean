-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_length_localized_eq_9df2ed0bc3a3
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_length_localized_eq_9df2ed0bc3a3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:15.45092+00:00
-- url     : https://prove2.me/theorems/0484825a-22a9-421a-b51a-13bb9ed04f68
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle length localized eq 9df2ed0bc3a3: P2 M Ground Theory Heights  Heights Section Cycle length localized eq 9df2ed0bc3a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle length localized eq 9df2ed0bc3a3 construction uses the P2 M Ground Theory Heights  Heights Section Cycle length localized eq 9df2ed0bc3a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L17-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L17-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
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
open GroundTheory.Heights₂.Heights.SectionCycle
variable {S : Type*} [CommRing S]

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_length_localized_eq_9df2ed0bc3a3 {J J₁ W : Ideal S} [W.IsPrime] (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J₁)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«length_localized_eq» := P2M_GroundTheory_Heights__Heights_SectionCycle_length_localized_eq_9df2ed0bc3a3
