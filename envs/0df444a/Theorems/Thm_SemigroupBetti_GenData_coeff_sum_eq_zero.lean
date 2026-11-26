-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_coeff_sum_eq_zero
-- name    : SemigroupBetti.GenData.coeff_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:23.699951+00:00
-- url     : https://prove2.me/theorems/99c32edb-aadd-561f-a074-30a795d7ae00
-- title:
--   Gen Data: coeff sum eq zero
-- statement:
--   **Lemma 0B.** An element of the kernel has zero coefficient sum on every fiber.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L243-L251
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Bridge.lean#L243-L251

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]

theorem SemigroupBetti.GenData.coeff_sum_eq_zero {f : MvPolynomial (Fin 4) K} (hf : f ∈ G.toricKer K) (d : ℕ) :
    ∑ s ∈ f.support.filter (fun s : Fin 4 →₀ ℕ => G.nu ⇑s = d), f.coeff s = 0 := by sorry
