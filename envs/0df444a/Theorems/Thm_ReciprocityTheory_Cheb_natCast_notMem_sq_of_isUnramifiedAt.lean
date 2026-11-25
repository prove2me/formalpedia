-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_natCast_notMem_sq_of_isUnramifiedAt
-- name    : ReciprocityTheory.Cheb.natCast_notMem_sq_of_isUnramifiedAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:07.531038+00:00
-- url     : https://prove2.me/theorems/ede991c4-b41d-4d44-90ef-9a45b1595a11
-- title:
--   Cheb: nat Cast not Mem sq of is Unramified At
-- statement:
--   The Cheb construction uses the nat Cast not Mem sq of is Unramified At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L40-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L40-L77

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

theorem ReciprocityTheory.Cheb.natCast_notMem_sq_of_isUnramifiedAt {K : Type*} [Field K] [NumberField K] {l : ℕ}
    (hl : l.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [Algebra.IsUnramifiedAt ℤ P] : (l : 𝓞 K) ∉ P ^ 2 := by sorry
