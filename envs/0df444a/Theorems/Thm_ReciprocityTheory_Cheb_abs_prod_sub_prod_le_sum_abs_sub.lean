-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_abs_prod_sub_prod_le_sum_abs_sub
-- name    : ReciprocityTheory.Cheb.abs_prod_sub_prod_le_sum_abs_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:51.483023+00:00
-- url     : https://prove2.me/theorems/9c02b747-7bbc-47df-a6cd-3add528a096f
-- title:
--   Cheb: abs prod sub prod le sum abs sub
-- statement:
--   The Cheb construction uses the abs prod sub prod le sum abs sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L59-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L59-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.abs_prod_sub_prod_le_sum_abs_sub {κ : Type*} (s : Finset κ) (a b : κ → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by sorry
