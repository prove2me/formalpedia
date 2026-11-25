-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreClass_eq_prod_76f68d661d7a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreClass_eq_prod_76f68d661d7a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:29.4107+00:00
-- url     : https://prove2.me/theorems/04057790-0ec5-4584-adfd-ec2b26382935
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top fibre Class eq prod 76f68d661d7a: P2 M Ground Theory Heights  Heights Rest Terms Top fibre Class eq prod 76f68d661d7a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top fibre Class eq prod 76f68d661d7a construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top fibre Class eq prod 76f68d661d7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L135-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L135-L142

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreClass_eq_prod_76f68d661d7a (f r a : ℕ) (c : SmallBlock) :
    fibreClass f r a c = ∏ σ : Fin f, blockEmb f (r + a) σ (fib1 r a c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«fibreClass_eq_prod» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_fibreClass_eq_prod_76f68d661d7a
