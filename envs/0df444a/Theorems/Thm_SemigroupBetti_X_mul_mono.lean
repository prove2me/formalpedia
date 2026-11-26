-- Prove2me | Theorems.Thm_SemigroupBetti_X_mul_mono
-- name    : SemigroupBetti.X_mul_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:53:35.39491+00:00
-- url     : https://prove2.me/theorems/ce14a2c8-71a6-4476-bbc1-849a8d95ab9d
-- title:
--   Semigroup Betti: X mul mono
-- statement:
--   The Semigroup Betti construction uses the X mul mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L63-L72
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L63-L72

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

theorem SemigroupBetti.X_mul_mono (i : Fin 4) (u : Fin 4 → ℕ) :
    (X i : MvPolynomial (Fin 4) K) * mono K u = mono K (u + Pi.single i 1) := by sorry
