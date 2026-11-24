-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_forall_isUnramifiedAt
-- name    : ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:19.304422+00:00
-- url     : https://prove2.me/theorems/c29e876b-143d-4b8a-8440-05d800dc72fa
-- title:
--   Cheb: exists forall is Unramified At
-- statement:
--   The Cheb construction uses the exists forall is Unramified At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L32-L38

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

theorem ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt (K : Type*) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N < p → ∀ (P : Ideal (𝓞 K)) [P.IsPrime], (p : 𝓞 K) ∈ P →
      Algebra.IsUnramifiedAt ℤ P := by sorry
