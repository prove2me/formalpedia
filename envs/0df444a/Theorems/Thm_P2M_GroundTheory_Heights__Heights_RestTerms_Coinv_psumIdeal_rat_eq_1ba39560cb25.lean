-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_rat_eq_1ba39560cb25
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_rat_eq_1ba39560cb25
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:19:09.964173+00:00
-- url     : https://prove2.me/theorems/9d4e1e55-a2e7-4298-a30d-8001d43ac986
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal rat eq 1ba39560cb25: P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal rat eq 1ba39560cb25
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal rat eq 1ba39560cb25 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal rat eq 1ba39560cb25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvariantTopDegree.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvariantTopDegree.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvariantTopDegree
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_rat_eq_1ba39560cb25 (f N : ℕ) :
    Coinv.psumIdeal ℚ f N =
      Ideal.span {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = blockPowerSum f N k τ} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«psumIdeal_rat_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_rat_eq_1ba39560cb25
