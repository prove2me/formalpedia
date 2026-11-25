-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_cyclotomic_irreducible_of_isUnramifiedAt
-- name    : ReciprocityTheory.Cheb.cyclotomic_irreducible_of_isUnramifiedAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:41.335439+00:00
-- url     : https://prove2.me/theorems/ea4b0498-fbc4-574d-945d-79d7469c796f
-- title:
--   Cheb: cyclotomic irreducible of is Unramified At
-- statement:
--   The Cheb construction uses the cyclotomic irreducible of is Unramified At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L79-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L79-L124

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

theorem ReciprocityTheory.Cheb.cyclotomic_irreducible_of_isUnramifiedAt {K : Type*} [Field K] [NumberField K] {l : ℕ}
    (hl : l.Prime) (P : Ideal (𝓞 K)) [P.IsPrime] (hlP : (l : 𝓞 K) ∈ P)
    [Algebra.IsUnramifiedAt ℤ P] : Irreducible (cyclotomic l K) := by sorry
