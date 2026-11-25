-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_forall_cyclotomic_irreducible
-- name    : ReciprocityTheory.Cheb.exists_forall_cyclotomic_irreducible
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:55.316369+00:00
-- url     : https://prove2.me/theorems/35d6eb8c-189c-4baa-b236-1f8ba10fdf10
-- title:
--   Cheb: exists forall cyclotomic irreducible
-- statement:
--   The Cheb construction uses the exists forall cyclotomic irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L156-L160

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

theorem ReciprocityTheory.Cheb.exists_forall_cyclotomic_irreducible (K : Type*) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ l : ℕ, l.Prime → N < l → Irreducible (cyclotomic l K) := by sorry
