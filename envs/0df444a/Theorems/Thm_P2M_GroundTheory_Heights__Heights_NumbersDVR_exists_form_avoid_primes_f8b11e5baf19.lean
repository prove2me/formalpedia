-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_avoid_primes_f8b11e5baf19
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_avoid_primes_f8b11e5baf19
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:32.801124+00:00
-- url     : https://prove2.me/theorems/7345b645-bc49-406c-a322-29a04c845831
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists form avoid primes f8b11e5baf19: P2 M Ground Theory Heights  Heights Numbers DVR exists form avoid primes f8b11e5baf19
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists form avoid primes f8b11e5baf19 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists form avoid primes f8b11e5baf19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RelevantMinimalOfDivCycleNeZero.lean#L19-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RelevantMinimalOfDivCycleNeZero.lean#L19-L62

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_avoid_primes_f8b11e5baf19 (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ W ∈ S, W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W) (e₀ : K → ℕ) :
    ∃ (e : K → ℕ) (h : MRing ι R), IsMultiHomog h e ∧ e₀ ≤ e ∧ ∀ W ∈ S, h ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_form_avoid_primes» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_avoid_primes_f8b11e5baf19
