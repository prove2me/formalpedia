-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_cyclotomic_irreducible_of_forall_isUnramifiedAt
-- name    : ReciprocityTheory.Cheb.cyclotomic_irreducible_of_forall_isUnramifiedAt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:36:45.123822+00:00
-- url     : https://prove2.me/theorems/c1d63103-f5c7-45d5-aab9-76c39594f020
-- title:
--   Cheb: cyclotomic irreducible of forall is Unramified At
-- statement:
--   The Cheb construction uses the cyclotomic irreducible of forall is Unramified At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L139-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L139-L154

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

theorem ReciprocityTheory.Cheb.cyclotomic_irreducible_of_forall_isUnramifiedAt {K : Type*} [Field K] [NumberField K]
    {l : ℕ} (hl : l.Prime)
    (h : ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (l : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt ℤ P) :
    Irreducible (cyclotomic l K) := by sorry
