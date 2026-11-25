-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_cons_zero_9549e2b329f7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_cons_zero_9549e2b329f7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:12:41.417714+00:00
-- url     : https://prove2.me/theorems/70f895f3-abe5-42d5-bc78-0b4f02a297a2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR v Num cons zero 9549e2b329f7: P2 M Ground Theory Heights  Heights Numbers DVR v Num cons zero 9549e2b329f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR v Num cons zero 9549e2b329f7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR v Num cons zero 9549e2b329f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L41-L44

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_cons_zero_9549e2b329f7 {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (W : Ideal (MRing ι O)) {n : ℕ}
    (L : Fin n → K → ℤ) : vNum W (Matrix.vecCons 0 L) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«vNum_cons_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_cons_zero_9549e2b329f7
