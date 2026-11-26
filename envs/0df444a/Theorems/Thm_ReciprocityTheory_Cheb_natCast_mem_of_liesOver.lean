-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_natCast_mem_of_liesOver
-- name    : ReciprocityTheory.Cheb.natCast_mem_of_liesOver
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:09.885601+00:00
-- url     : https://prove2.me/theorems/d99a1fa3-611d-46ae-bde5-d3605c87674d
-- title:
--   Cheb: nat Cast mem of lies Over
-- statement:
--   The Cheb construction uses the nat Cast mem of lies Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean#L126-L131

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

theorem ReciprocityTheory.Cheb.natCast_mem_of_liesOver {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (P : Ideal (𝓞 K)) [P.LiesOver (Ideal.span {(p : ℤ)})] : (p : 𝓞 K) ∈ P := by sorry
