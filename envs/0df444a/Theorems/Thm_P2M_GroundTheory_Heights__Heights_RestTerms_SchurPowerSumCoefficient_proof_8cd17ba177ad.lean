-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchurPowerSumCoefficient_proof_8cd17ba177ad
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchurPowerSumCoefficient_proof_8cd17ba177ad
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:01:09.603826+00:00
-- url     : https://prove2.me/theorems/86149177-1cd9-435c-870f-d21452eef3d5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur Power Sum Coefficient proof 8cd17ba177ad: P2 M Ground Theory Heights  Heights Rest Terms Schur Power Sum Coefficient proof 8cd17ba177ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur Power Sum Coefficient proof 8cd17ba177ad construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur Power Sum Coefficient proof 8cd17ba177ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchurPowerSumCoefficient.lean#L13-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchurPowerSumCoefficient.lean#L13-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchurPowerSumCoefficient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchurPowerSumCoefficient_proof_8cd17ba177ad (h1 : SchWeightedPreimage.Statement)
    (h2 : SchEvalPowerSumHom.Statement) (h3 : SchSchurHomogeneous.Statement)
    (h4 : SchSchurAtRootsOfUnity.Statement) : SchurPowerSumCoefficient.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchurPowerSumCoefficient».«proof» := P2M_GroundTheory_Heights__Heights_RestTerms_SchurPowerSumCoefficient_proof_8cd17ba177ad
