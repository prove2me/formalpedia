-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_cons_zero_c2d9a9f8b276
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_cons_zero_c2d9a9f8b276
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:32.388795+00:00
-- url     : https://prove2.me/theorems/0d9154b4-6596-45d7-8f6a-ba87f1176591
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mixed Diff cons zero c2d9a9f8b276: P2 M Ground Theory Heights  Heights Numbers DVR mixed Diff cons zero c2d9a9f8b276
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mixed Diff cons zero c2d9a9f8b276 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mixed Diff cons zero c2d9a9f8b276 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L27-L32

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_cons_zero_c2d9a9f8b276 {K : Type*} {n : ℕ} (L : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Matrix.vecCons 0 L) h = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mixedDiff_cons_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_cons_zero_c2d9a9f8b276
