-- Prove2me | Theorems.Thm_SemigroupBetti_toricMap_monomial
-- name    : SemigroupBetti.toricMap_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:53:05.719412+00:00
-- url     : https://prove2.me/theorems/ad56bb4a-442d-4cf3-bbc4-6e8756e7e024
-- title:
--   Semigroup Betti: toric Map monomial
-- statement:
--   The Semigroup Betti construction uses the toric Map monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L55-L61
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L55-L61

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

theorem SemigroupBetti.toricMap_monomial (n : Fin 4 → ℕ) (s : Fin 4 →₀ ℕ) (c : K) :
    toricMap K n (monomial s c) = Polynomial.C c * Polynomial.X ^ (∑ i, s i * n i) := by sorry
