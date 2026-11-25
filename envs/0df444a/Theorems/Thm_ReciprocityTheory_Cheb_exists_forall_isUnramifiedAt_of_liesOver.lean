-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_forall_isUnramifiedAt_of_liesOver
-- name    : ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt_of_liesOver
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:35.949729+00:00
-- url     : https://prove2.me/theorems/e328b6dd-d80a-5f1a-bcfc-a4c7f94db641
-- title:
--   Cheb: exists forall is Unramified At of lies Over
-- statement:
--   The Cheb construction uses the exists forall is Unramified At of lies Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L133-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L133-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Polynomial NumberField

theorem ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt_of_liesOver (K : Type*) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N < p → ∀ (P : Ideal (𝓞 K)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], Algebra.IsUnramifiedAt ℤ P := by sorry
