-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_eq_bot_of_not_mem_1f5ac74ee822
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_eq_bot_of_not_mem_1f5ac74ee822
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:44.153027+00:00
-- url     : https://prove2.me/theorems/c187efd4-b8a0-49aa-8fb5-70d9ac1898ec
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR comap C eq bot of not mem 1f5ac74ee822: P2 M Ground Theory Heights  Heights Numbers DVR comap C eq bot of not mem 1f5ac74ee822
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR comap C eq bot of not mem 1f5ac74ee822 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR comap C eq bot of not mem 1f5ac74ee822 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L46-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
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
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_eq_bot_of_not_mem_1f5ac74ee822 {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (H : Ideal (MRing ι O)) [hH : H.IsPrime] (hϖH : (C ϖ : MRing ι O) ∉ H) :
    H.comap (C : O →+* MRing ι O) = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«comap_C_eq_bot_of_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_eq_bot_of_not_mem_1f5ac74ee822
