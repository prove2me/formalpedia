-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_eq_of_certificates
-- name    : SizeRamsey.Plan.tau4_eq_of_certificates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:31.072371+00:00
-- url     : https://prove2.me/theorems/e3828c18-b643-4c5a-b866-70a7bb1c4829
-- title:
--   Plan: tau4 eq of certificates
-- statement:
--   The Plan construction uses the tau4 eq of certificates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L126-L136
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L126-L136

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.tau4_eq_of_certificates
    {V : Type u} [Fintype V] {G : SimpleGraph V} (k : ℕ)
    (hupper : ∃ S : Finset V, c4Transversal G S ∧ S.card = k)
    (hlower : ∀ S : Finset V,
      S.card < k → ¬ c4Transversal G S) :
    tau4 G = k := by sorry
