-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_fundCycle_support_ac08cec74a0f
-- name    : P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_fundCycle_support_ac08cec74a0f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:35.531552+00:00
-- url     : https://prove2.me/theorems/bd7a967b-9bbd-5494-8108-cc9933b0709f
-- title:
--   P2 M Ground Theory Heights  Heights mem minimal Primes of mem fund Cycle support ac08cec74a0f: P2 M Ground Theory Heights  Heights mem minimal Primes of mem fund Cycle support ac08cec74a0f
-- statement:
--   The P2 M Ground Theory Heights  Heights mem minimal Primes of mem fund Cycle support ac08cec74a0f construction uses the P2 M Ground Theory Heights  Heights mem minimal Primes of mem fund Cycle support ac08cec74a0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MemMinimalPrimesOfMemFundCycleSupport.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MemMinimalPrimesOfMemFundCycleSupport.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ComplexFibreIdealBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar ptsIntegral pot)

theorem P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_fundCycle_support_ac08cec74a0f {n : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    (hW : W ∈ (fundCycle J).support) : W ∈ J.minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_minimalPrimes_of_mem_fundCycle_support» := P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_fundCycle_support_ac08cec74a0f
