-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallPowerSum_mul_restPolynomial_d2f1e6c17816
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallPowerSum_mul_restPolynomial_d2f1e6c17816
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:59.3197+00:00
-- url     : https://prove2.me/theorems/8e54f9ab-9766-418e-80d9-00e60000e4b5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top small Power Sum mul rest Polynomial d2f1e6c17816: P2 M Ground Theory Heights  Heights Rest Terms Top small Power Sum mul rest Polynomial d2f1e6c17816
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top small Power Sum mul rest Polynomial d2f1e6c17816 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top small Power Sum mul rest Polynomial d2f1e6c17816 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L130-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L130-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallPowerSum_mul_restPolynomial_d2f1e6c17816 (f r a : ℕ) (c : SmallBlock) (k : ℕ) (hk : 2 ≤ k)
    (τ : Fin f) :
    smallPowerSum f r a c (k - 1) τ * restPolynomial f r a c =
      gmf f r a c (fun σ => if σ = τ then k - 1 else 0) (f * (r * a) + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«smallPowerSum_mul_restPolynomial» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallPowerSum_mul_restPolynomial_d2f1e6c17816
