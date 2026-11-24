-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAtTop_proof_7264ddd9e7c0
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAtTop_proof_7264ddd9e7c0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:04.308882+00:00
-- url     : https://prove2.me/theorems/7d25b3bd-8ba5-4cab-b73b-0dbc2534ccf2
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv At Top proof 7264ddd9e7c0: P2 M Ground Theory Heights  Heights Rest Terms Coinv At Top proof 7264ddd9e7c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv At Top proof 7264ddd9e7c0 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv At Top proof 7264ddd9e7c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvAtTop.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvAtTop.lean#L11-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvAtTop
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAtTop_proof_7264ddd9e7c0 (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAtTop.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CoinvAtTop».«proof» := P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAtTop_proof_7264ddd9e7c0
