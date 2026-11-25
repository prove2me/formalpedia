-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_coeff_aeval_diagonal_0e15d31de021
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_coeff_aeval_diagonal_0e15d31de021
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:54.028909+00:00
-- url     : https://prove2.me/theorems/12658067-af6d-551a-92e9-8875a138f50c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur Sign Coefficient coeff aeval diagonal 0e15d31de021: P2 M Ground Theory Heights  Heights Rest Terms Schur Sign Coefficient coeff aeval diagonal 0e15
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur Sign Coefficient coeff aeval diagonal 0e15d31de021 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur Sign Coefficient coeff aeval diagonal 0e15d31de021 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchurSignCoefficient.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchurSignCoefficient.lean#L13-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchurSignCoefficient
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_coeff_aeval_diagonal_0e15d31de021 {N : ℕ} (c : Fin N → ℚ)
    (P : MvPolynomial (Fin N) ℚ) (e : Fin N →₀ ℕ) :
    coeff e (aeval (fun i : Fin N => C (c i) * X i) P) = (∏ i, c i ^ e i) * coeff e P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchurSignCoefficient».«coeff_aeval_diagonal» := P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_coeff_aeval_diagonal_0e15d31de021
