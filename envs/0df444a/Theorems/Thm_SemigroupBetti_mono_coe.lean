-- Prove2me | Theorems.Thm_SemigroupBetti_mono_coe
-- name    : SemigroupBetti.mono_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:52:55.591097+00:00
-- url     : https://prove2.me/theorems/40970945-47e6-5e7d-aa4f-b91eb136b266
-- title:
--   Semigroup Betti: mono coe
-- statement:
--   The Semigroup Betti construction uses the mono coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L52-L53
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L52-L53

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
variable (K : Type*) [Field K]
variable {K}

theorem SemigroupBetti.mono_coe (s : Fin 4 →₀ ℕ) : mono K ⇑s = monomial s 1 := by sorry
