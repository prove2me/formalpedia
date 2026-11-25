-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_ringKrullDim_1e2c6b73d0ff
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_ringKrullDim_1e2c6b73d0ff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:20.11348+00:00
-- url     : https://prove2.me/theorems/a3bca24d-7b4b-42f4-8182-3de029dae760
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of ring Krull Dim 1e2c6b73d0ff: P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of ring Krull Dim 1e2c6b73d0ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of ring Krull Dim 1e2c6b73d0ff construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of ring Krull Dim 1e2c6b73d0ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RingKrullDimQuotientLeComapAddOne.lean#L55-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RingKrullDimQuotientLeComapAddOne.lean#L55-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RingKrullDimQuotientLeComapAddOne
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_ringKrullDim_1e2c6b73d0ff {A : Type*} [CommRing A] (P G : Ideal A) [P.IsPrime]
    [G.IsPrime] (s : A) (hsP : s ∉ P) (N : ℕ) (hP : ringKrullDim (A ⧸ P) = (N : WithBot ℕ∞))
    (hle : P ⊔ Ideal.span {s} ≤ G) (hG : (N : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ G) + 1) :
    G ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_minimalPrimes_of_ringKrullDim» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_ringKrullDim_1e2c6b73d0ff
