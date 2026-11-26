-- Prove2me | Theorems.Thm_SemigroupBetti_sharesVar_iff_supp
-- name    : SemigroupBetti.sharesVar_iff_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:31.70232+00:00
-- url     : https://prove2.me/theorems/5e1e5fc8-df53-5cf1-9f78-5e1542e59338
-- title:
--   Semigroup Betti: shares Var iff supp
-- statement:
--   The Semigroup Betti construction uses the shares Var iff supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L60-L62
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Defs.lean#L60-L62

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset

theorem SemigroupBetti.sharesVar_iff_supp {z z' : Fin 4 → ℕ} :
    SharesVar z z' ↔ ¬ Disjoint (supp z) (supp z') := by sorry
