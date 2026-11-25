-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_ne_zero_facts_17d796702cc2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_ne_zero_facts_17d796702cc2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:10:41.616515+00:00
-- url     : https://prove2.me/theorems/da9e3c5e-cb2c-4215-a7a8-15337f59ff48
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle ne zero facts 17d796702cc2: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle ne zero facts 17d796702cc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle ne zero facts 17d796702cc2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle ne zero facts 17d796702cc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/DivCycleNeZeroFacts.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/DivCycleNeZeroFacts.lean#L13-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivCycleNeZeroFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_ne_zero_facts_17d796702cc2 {O : Type u} [CommRing O] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {P : Ideal (MRing ι O)} (hP : IsMultiHomogIdeal P) {f : MRing ι O} {e : K → ℕ}
    (hf : IsMultiHomog f e) {W : Ideal (MRing ι O)} (h : divCycle P f W ≠ 0) :
    W.IsPrime ∧ IsRelevant W ∧ P ≤ W ∧ IsMultiHomogIdeal W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_ne_zero_facts» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_ne_zero_facts_17d796702cc2
