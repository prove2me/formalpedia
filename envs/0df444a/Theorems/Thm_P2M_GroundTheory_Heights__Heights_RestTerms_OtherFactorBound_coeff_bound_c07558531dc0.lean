-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_coeff_bound_c07558531dc0
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_coeff_bound_c07558531dc0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:16.568485+00:00
-- url     : https://prove2.me/theorems/daec90e3-836c-47bc-9c0e-2941de1b1808
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Other Factor Bound coeff bound c07558531dc0: P2 M Ground Theory Heights  Heights Rest Terms Other Factor Bound coeff bound c07558531dc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Other Factor Bound coeff bound c07558531dc0 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Other Factor Bound coeff bound c07558531dc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/POtherFactorBound.lean#L21-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/POtherFactorBound.lean#L21-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_POtherFactorBound
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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_coeff_bound_c07558531dc0 (hS : SchurSignCoefficient.Statement)
    (hH : HookSumBound.Statement) (r a k : ℕ) (c : SmallBlock) (hk1 : 1 ≤ k) (hkN : k ≤ r + a)
    (S : MvPolynomial (Fin (r + a)) ℚ)
    (hSeq : powerSumHom (r + a) S =
      ∑ nu ∈ partitionsOf r k,
        C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
          aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu)) :
    |coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1) S| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«OtherFactorBound».«coeff_bound» := P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_coeff_bound_c07558531dc0
