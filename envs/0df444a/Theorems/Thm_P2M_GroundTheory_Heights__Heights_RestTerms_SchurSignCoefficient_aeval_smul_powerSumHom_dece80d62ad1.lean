-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_aeval_smul_powerSumHom_dece80d62ad1
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_aeval_smul_powerSumHom_dece80d62ad1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:51.37021+00:00
-- url     : https://prove2.me/theorems/6af6d45e-c649-4af5-bbc8-d48e834f2c55
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur Sign Coefficient aeval smul power Sum Hom dece80d62ad1: P2 M Ground Theory Heights  Heights Rest Terms Schur Sign Coefficient aeval smul power Sum
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur Sign Coefficient aeval smul power Sum Hom dece80d62ad1 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur Sign Coefficient aeval smul power Sum Hom dece80d62ad1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchurSignCoefficient.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchurSignCoefficient.lean#L30-L40

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_aeval_smul_powerSumHom_dece80d62ad1 (N : ℕ) (s : ℚ)
    (S : MvPolynomial (Fin N) ℚ) :
    aeval (fun i : Fin N => C s * X i) (powerSumHom N S) =
      powerSumHom N (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchurSignCoefficient».«aeval_smul_powerSumHom» := P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_aeval_smul_powerSumHom_dece80d62ad1
