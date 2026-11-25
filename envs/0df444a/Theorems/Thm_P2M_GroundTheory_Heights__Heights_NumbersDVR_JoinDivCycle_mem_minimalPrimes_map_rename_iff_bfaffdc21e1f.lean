-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_mem_minimalPrimes_map_rename_iff_bfaffdc21e1f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_mem_minimalPrimes_map_rename_iff_bfaffdc21e1f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:59:35.05484+00:00
-- url     : https://prove2.me/theorems/8d1d7dbc-e91f-4f44-8a1c-aa99af82d9dd
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle mem minimal Primes map rename iff bfaffdc21e1f: P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle mem minimal Primes map ren
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle mem minimal Primes map rename iff bfaffdc21e1f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Div Cycle mem minimal Primes map rename iff bfaffdc21e1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L86-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinDivCycle.lean#L86-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinDivCycle
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinDivCycle
variable {R : Type} [CommRing R] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
local notation "ψ" => joinPolyEquiv (R := R) (ι := ι)
local notation "ε" => rename (R := R) (liftVar (ι := ι) ptIdx)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_mem_minimalPrimes_map_rename_iff_bfaffdc21e1f (J : Ideal (MRing ι R))
    (W : Ideal (MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R)) :
    W ∈ (J.map ε).minimalPrimes ↔ ∃ Q ∈ J.minimalPrimes, Q.map ε = W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinDivCycle».«mem_minimalPrimes_map_rename_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinDivCycle_mem_minimalPrimes_map_rename_iff_bfaffdc21e1f
