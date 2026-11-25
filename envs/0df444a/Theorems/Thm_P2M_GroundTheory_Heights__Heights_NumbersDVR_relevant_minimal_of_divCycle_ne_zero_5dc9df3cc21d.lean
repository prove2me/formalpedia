-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_relevant_minimal_of_divCycle_ne_zero_5dc9df3cc21d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_relevant_minimal_of_divCycle_ne_zero_5dc9df3cc21d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:13.481904+00:00
-- url     : https://prove2.me/theorems/e8ae3522-487a-4dfb-b5ca-0159a0658fee
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR relevant minimal of div Cycle ne zero 5dc9df3cc21d: P2 M Ground Theory Heights  Heights Numbers DVR relevant minimal of div Cycle ne zero 5dc9df3cc21d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR relevant minimal of div Cycle ne zero 5dc9df3cc21d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR relevant minimal of div Cycle ne zero 5dc9df3cc21d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RelevantMinimalOfDivCycleNeZero.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RelevantMinimalOfDivCycleNeZero.lean#L98-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RelevantMinimalOfDivCycleNeZero
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_relevant_minimal_of_divCycle_ne_zero_5dc9df3cc21d {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P W : Ideal (MRing ι R)} {x : MRing ι R} (h : divCycle P x W ≠ 0) :
    W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«relevant_minimal_of_divCycle_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_relevant_minimal_of_divCycle_ne_zero_5dc9df3cc21d
