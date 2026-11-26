-- Prove2me | Theorems.Thm_SemigroupBetti_IsPairAntichain_fst_inj
-- name    : SemigroupBetti.IsPairAntichain.fst_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:57:37.43454+00:00
-- url     : https://prove2.me/theorems/5a8e3bd1-1211-539e-8ead-3568af6832f8
-- title:
--   Is Pair Antichain: fst inj
-- statement:
--   The Is Pair Antichain construction uses the fst inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L32-L36
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L32-L36

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
variable {T : Finset (ℕ × ℕ)}

theorem SemigroupBetti.IsPairAntichain.fst_inj (hT : IsPairAntichain T) {x y : ℕ × ℕ} (hx : x ∈ T) (hy : y ∈ T)
    (h : x.1 = y.1) : x = y := by sorry
