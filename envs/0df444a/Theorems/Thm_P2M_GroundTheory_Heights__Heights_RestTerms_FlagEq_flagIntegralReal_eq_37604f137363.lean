-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_flagIntegralReal_eq_37604f137363
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_flagIntegralReal_eq_37604f137363
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:32.273801+00:00
-- url     : https://prove2.me/theorems/454166da-decf-4525-9dbb-84603484bcbb
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq flag Integral Real eq 37604f137363: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq flag Integral Real eq 37604f137363
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq flag Integral Real eq 37604f137363 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq flag Integral Real eq 37604f137363 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L23-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L23-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
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
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_flagIntegralReal_eq_37604f137363 {f N : ℕ} (G : MvPolynomial (Fin f × Fin N) ℝ) :
    flagIntegralReal f N G =
      stairConst f N * ∑ w, ((permSign f N w : ℤ) : ℝ) * coeff (stairExp f N w) G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«flagIntegralReal_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_flagIntegralReal_eq_37604f137363
