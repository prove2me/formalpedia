-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAboveTop_proof_4df83f60992a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAboveTop_proof_4df83f60992a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:01:54.578558+00:00
-- url     : https://prove2.me/theorems/d8790c57-901f-41d7-bd8c-5d64ed3359eb
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv Above Top proof 4df83f60992a: P2 M Ground Theory Heights  Heights Rest Terms Coinv Above Top proof 4df83f60992a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv Above Top proof 4df83f60992a construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv Above Top proof 4df83f60992a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvAboveTop.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvAboveTop.lean#L9-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvAboveTop
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
open MvPolynomial Finset Coinv

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAboveTop_proof_4df83f60992a (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAboveTop.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CoinvAboveTop».«proof» := P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAboveTop_proof_4df83f60992a
